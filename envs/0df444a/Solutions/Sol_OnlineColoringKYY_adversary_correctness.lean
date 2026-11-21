-- Prove2me | solution 1 for OnlineColoringKYY.adversary_correctness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:07:45.683263+00:00
-- url     : https://prove2.me/submissions/1bbe31e4-59f3-4bba-93c2-3e770927e34b

import Mathlib
import Definitions.Def_OnlineColoringKYY_OnlineColoringAlg
import Definitions.Def_OnlineColoringKYY_prefixGraph
import Definitions.Def_OnlineColoringKYY_run
import Definitions.Def_OnlineColoringKYY_IsProper
import Definitions.Def_OnlineColoringKYY_admits
import Definitions.Def_OnlineColoringKYY_baseColor
import Definitions.Def_OnlineColoringKYY_advEdge
import Definitions.Def_OnlineColoringKYY_stepGraph
import Definitions.Def_OnlineColoringKYY_advColors
import Definitions.Def_OnlineColoringKYY_advGraph
import Theorems.Thm_OnlineColoringKYY_adversary_no_third_vertex

section
set_option autoImplicit false

namespace OnlineColoringKYY.Dev.Common
open OnlineColoringKYY

theorem admits_lt {ℓ : ℕ} (code : ℕ → Fin ℓ → Bool) (j b : ℕ) (h : admits code j b) : b < 2 * ℓ := by
  obtain ⟨s, rfl⟩ := h
  have := s.isLt
  have := Bool.toNat_le (code j s)
  omega

theorem baseColor_spec {ℓ : ℕ} (code : ℕ → Fin ℓ → Bool) (u w : ℕ) (h : code u ≠ code w) :
    ∃ s : Fin ℓ, code u s ≠ code w s ∧ baseColor code u w = 2 * s.val + (code u s).toNat ∧
      baseColor code w u = 2 * s.val + (code w s).toNat := by
  have hne : (Finset.univ.filter (fun i : Fin ℓ => code u i ≠ code w i)).Nonempty := by
    by_contra hc
    apply h
    funext i
    by_contra hi
    exact hc ⟨i, by simpa using hi⟩
  have hne' : (Finset.univ.filter (fun i : Fin ℓ => code w i ≠ code u i)).Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, by simp at hi ⊢; exact fun e => hi e.symm⟩
  have hset : (Finset.univ.filter (fun i : Fin ℓ => code w i ≠ code u i)) =
      (Finset.univ.filter (fun i : Fin ℓ => code u i ≠ code w i)) := by
    ext i; simp [ne_comm]
  refine ⟨(Finset.univ.filter (fun i : Fin ℓ => code u i ≠ code w i)).min' hne, ?_, ?_, ?_⟩
  · have := Finset.min'_mem _ hne
    simpa using this
  · unfold baseColor; rw [dif_pos hne]
  · unfold baseColor; rw [dif_pos hne']
    simp only [hset]

theorem baseColor_admits {ℓ : ℕ} (code : ℕ → Fin ℓ → Bool) (u w : ℕ) (h : code u ≠ code w) :
    admits code u (baseColor code u w) := by
  obtain ⟨s, -, h1, -⟩ := baseColor_spec code u w h
  rw [h1]; exact ⟨s, rfl⟩

theorem advColors_stable' {ℓ : ℕ} (A : OnlineColoringAlg) (code : ℕ → Fin ℓ → Bool) (n w : ℕ)
    (hw : w < n) : advColors A code n w = advColors A code (w + 1) w := by
  obtain ⟨k, hk⟩ : ∃ k, n = w + 1 + k := ⟨n - (w + 1), by omega⟩
  subst hk
  exact advColors_stable A code (w + 1) k w (by omega)

theorem run_adv {ℓ : ℕ} (A : OnlineColoringAlg) (code : ℕ → Fin ℓ → Bool) (n : ℕ) (v : Fin n) :
    run A (advGraph A code n) v = advColors A code n v.val := by
  unfold run
  rw [prefixGraph_advGraph, advColors_stable' A code n v.val v.isLt, advColors]
  simp

theorem adj_adv {ℓ : ℕ} (A : OnlineColoringAlg) (code : ℕ → Fin ℓ → Bool) (n : ℕ) (i j : Fin n) :
    (advGraph A code n).Adj i j ↔
      (advEdge code (advColors A code n) i.val j.val ∨ advEdge code (advColors A code n) j.val i.val) := by
  simp only [advGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    rcases h with h | h <;> exact absurd h.1 (lt_irrefl _)

end OnlineColoringKYY.Dev.Common
end

section
set_option autoImplicit false

namespace OnlineColoringKYY
open OnlineColoringKYY.Dev.Common

theorem chk_adversary_correctness (ℓ n : ℕ) (hℓ : 1 ≤ ℓ) (code : ℕ → Fin ℓ → Bool)
    (hcode : Set.InjOn code (Set.Iio n)) (A : OnlineColoringAlg) (hA : IsProper A) :
    (advGraph A code n).Colorable (2 * ℓ) ∧
      ∀ ψ : Fin n → ℕ,
        (∀ v w : Fin n, v ≠ w → run A (advGraph A code n) v = run A (advGraph A code n) w →
            ψ v = baseColor code v.val w.val) →
        (∀ v : Fin n, (∀ w : Fin n, w ≠ v →
            run A (advGraph A code n) w ≠ run A (advGraph A code n) v) →
            admits code v.val (ψ v)) →
        (∀ u v : Fin n, (advGraph A code n).Adj u v → ψ u ≠ ψ v) ∧ ∀ v, ψ v < 2 * ℓ := by
  have hne : ∀ v w : Fin n, v ≠ w → code v.val ≠ code w.val := fun v w h e =>
    h (Fin.ext (hcode v.isLt w.isLt e))
  have hcol : ∀ v : Fin n, run A (advGraph A code n) v = advColors A code n v.val :=
    fun v => run_adv A code n v
  have main : ∀ ψ : Fin n → ℕ,
        (∀ v w : Fin n, v ≠ w → run A (advGraph A code n) v = run A (advGraph A code n) w →
            ψ v = baseColor code v.val w.val) →
        (∀ v : Fin n, (∀ w : Fin n, w ≠ v →
            run A (advGraph A code n) w ≠ run A (advGraph A code n) v) →
            admits code v.val (ψ v)) →
        (∀ u v : Fin n, (advGraph A code n).Adj u v → ψ u ≠ ψ v) ∧ ∀ v, ψ v < 2 * ℓ := by
    intro ψ h1 h2
    have hadm : ∀ v : Fin n, admits code v.val (ψ v) := by
      intro v
      by_cases hp : ∃ w : Fin n, w ≠ v ∧ run A (advGraph A code n) w = run A (advGraph A code n) v
      · obtain ⟨w, hw, hc⟩ := hp
        rw [h1 v w (Ne.symm hw) hc.symm]
        exact baseColor_admits code v.val w.val (hne v w (Ne.symm hw))
      · push Not at hp
        exact h2 v hp
    refine ⟨?_, fun v => admits_lt code _ _ (hadm v)⟩
    have edge : ∀ i j : Fin n, advEdge code (advColors A code n) i.val j.val → ψ i ≠ ψ j := by
      rintro i j ⟨hij, w, hw, hwi, hc, hna⟩
      have hwi' : (⟨w, by omega⟩ : Fin n) ≠ i := fun e => hwi (congrArg Fin.val e)
      have hc' : run A (advGraph A code n) i = run A (advGraph A code n) ⟨w, by omega⟩ := by
        rw [hcol, hcol]; exact hc.symm
      have := h1 i ⟨w, by omega⟩ (Ne.symm hwi') hc'
      intro he
      rw [this] at he
      exact hna (he ▸ hadm j)
    intro u v huv
    rw [adj_adv] at huv
    rcases huv with h | h
    · exact edge u v h
    · exact (edge v u h).symm
  refine ⟨?_, main⟩
  -- existence of ψ
  classical
  let ψ : Fin n → ℕ := fun v =>
    if h : ∃ w : Fin n, w ≠ v ∧ run A (advGraph A code n) w = run A (advGraph A code n) v then
      baseColor code v.val (Classical.choose h).val
    else (code v.val ⟨0, hℓ⟩).toNat
  have hψ1 : ∀ v w : Fin n, v ≠ w → run A (advGraph A code n) v = run A (advGraph A code n) w →
      ψ v = baseColor code v.val w.val := by
    intro v w hvw hc
    have h : ∃ w : Fin n, w ≠ v ∧ run A (advGraph A code n) w = run A (advGraph A code n) v :=
      ⟨w, Ne.symm hvw, hc.symm⟩
    simp only [ψ, dif_pos h]
    have hs := Classical.choose_spec h
    have hle := OnlineColoringKYY.adversary_no_third_vertex ℓ n code hcode A hA
      (run A (advGraph A code n) v)
    have hweq : Classical.choose h = w := by
      by_contra hne'
      have : 2 < (Finset.univ.filter (fun u : Fin n =>
          run A (advGraph A code n) u = run A (advGraph A code n) v)).card := by
        rw [Finset.two_lt_card_iff]
        refine ⟨v, w, Classical.choose h, by simp, by simp [hc.symm], by simp [hs.2], hvw,
          Ne.symm hs.1, fun e => hne' e.symm⟩
      omega
    rw [hweq]
  have hψ2 : ∀ v : Fin n, (∀ w : Fin n, w ≠ v →
      run A (advGraph A code n) w ≠ run A (advGraph A code n) v) → admits code v.val (ψ v) := by
    intro v hv
    have h : ¬ ∃ w : Fin n, w ≠ v ∧ run A (advGraph A code n) w = run A (advGraph A code n) v :=
      fun ⟨w, hw, hc⟩ => hv w hw hc
    simp only [ψ, dif_neg h]
    exact ⟨⟨0, hℓ⟩, by simp⟩
  obtain ⟨hp, hb⟩ := main ψ hψ1 hψ2
  exact ⟨SimpleGraph.Coloring.mk (fun v => ⟨ψ v, hb v⟩) (fun {u v} huv e => hp u v huv (by simpa using congrArg Fin.val e))⟩

end OnlineColoringKYY
end

theorem solution : type_of% @OnlineColoringKYY.chk_adversary_correctness := @OnlineColoringKYY.chk_adversary_correctness
