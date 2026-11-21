-- Prove2me | solution 1 for OnlineColoringKYY.adversary_no_third_vertex
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:07:45.594632+00:00
-- url     : https://prove2.me/submissions/e979feef-87eb-4a09-8088-72530fef639e

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

section
set_option autoImplicit false

namespace OnlineColoringKYY.Dev.Common
open OnlineColoringKYY

theorem admits_iff {ℓ : ℕ} (code : ℕ → Fin ℓ → Bool) (j : ℕ) (s : Fin ℓ) (b : Bool) :
    admits code j (2 * s.val + b.toNat) ↔ code j s = b := by
  constructor
  · rintro ⟨s', h⟩
    have h1 : (code j s').toNat ≤ 1 := Bool.toNat_le _
    have h2 : b.toNat ≤ 1 := Bool.toNat_le _
    have hs : s' = s := Fin.ext (by omega)
    subst hs
    cases hb : code j s' <;> cases b <;> simp_all
  · intro h
    exact ⟨s, by rw [h]⟩

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

/-- one of the two base colors of a pair is not admitted by `j`. -/
theorem baseColor_not_both {ℓ : ℕ} (code : ℕ → Fin ℓ → Bool) (u w j : ℕ) (h : code u ≠ code w) :
    ¬ admits code j (baseColor code u w) ∨ ¬ admits code j (baseColor code w u) := by
  obtain ⟨s, hs, h1, h2⟩ := baseColor_spec code u w h
  rw [h1, h2, admits_iff, admits_iff]
  by_contra hc
  push_neg at hc
  obtain ⟨a, b⟩ := hc
  exact hs (a.symm.trans b)

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

theorem chk_adversary_no_third_vertex (ℓ n : ℕ) (code : ℕ → Fin ℓ → Bool)
    (hcode : Set.InjOn code (Set.Iio n)) (A : OnlineColoringAlg) (hA : IsProper A) (c : ℕ) :
    (Finset.univ.filter (fun v : Fin n => run A (advGraph A code n) v = c)).card ≤ 2 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (show 3 ≤ _ from hlt)
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hcard
  -- same color for all three
  have hc : ∀ v ∈ ({x, y, z} : Finset (Fin n)), run A (advGraph A code n) v = c := by
    intro v hv; exact (Finset.mem_filter.mp (hS hv)).2
  have cx := hc x (by simp)
  have cy := hc y (by simp)
  have cz := hc z (by simp)
  -- general claim: for distinct a b j with a, b < j same color as j: contradiction
  have key : ∀ a b j : Fin n, a.val < j.val → b.val < j.val → a ≠ b →
      run A (advGraph A code n) a = c → run A (advGraph A code n) b = c →
      run A (advGraph A code n) j = c → False := by
    intro a b j haj hbj hab ca cb cj
    have hne : code a.val ≠ code b.val := fun h =>
      hab (Fin.ext (hcode a.isLt b.isLt h))
    have hcol : ∀ v : Fin n, run A (advGraph A code n) v = advColors A code n v.val :=
      fun v => run_adv A code n v
    rcases baseColor_not_both code a.val b.val j.val hne with h | h
    · -- a is adjacent to j
      have hadj : (advGraph A code n).Adj a j := by
        rw [adj_adv]; left
        refine ⟨haj, b.val, hbj, fun e => hab (Fin.ext e.symm), ?_, h⟩
        rw [← hcol, ← hcol, ca, cb]
      exact hA n _ a j hadj (ca.trans cj.symm)
    · have hadj : (advGraph A code n).Adj b j := by
        rw [adj_adv]; left
        refine ⟨hbj, a.val, haj, fun e => hab (Fin.ext e), ?_, h⟩
        rw [← hcol, ← hcol, ca, cb]
      exact hA n _ b j hadj (cb.trans cj.symm)
  -- take the largest of x y z
  rcases lt_trichotomy x y with h1 | h1 | h1
  · rcases lt_trichotomy y z with h2 | h2 | h2
    · exact key x y z (Fin.lt_def.mp (h1.trans h2)) (Fin.lt_def.mp h2) hxy cx cy cz
    · exact hyz h2
    · exact key x z y (Fin.lt_def.mp h1) (Fin.lt_def.mp h2) hxz cx cz cy
  · exact hxy h1
  · rcases lt_trichotomy x z with h3 | h3 | h3
    · exact key y x z (Fin.lt_def.mp (h1.trans h3)) (Fin.lt_def.mp h3) (Ne.symm hxy) cy cx cz
    · exact hxz h3
    · rcases lt_trichotomy y z with h2 | h2 | h2
      · exact key y z x (Fin.lt_def.mp h1) (Fin.lt_def.mp h3) hyz cy cz cx
      · exact hyz h2
      · exact key z y x (Fin.lt_def.mp (h2.trans h1)) (Fin.lt_def.mp h1) (Ne.symm hyz) cz cy cx

end OnlineColoringKYY
end

theorem solution : type_of% @OnlineColoringKYY.chk_adversary_no_third_vertex := @OnlineColoringKYY.chk_adversary_no_third_vertex
