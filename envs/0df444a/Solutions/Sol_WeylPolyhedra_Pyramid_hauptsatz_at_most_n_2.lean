-- Prove2me | solution 2 for WeylPolyhedra.Pyramid.hauptsatz_at_most_n
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T11:42:59.922739+00:00
-- url     : https://prove2.me/submissions/3be5e012-a303-42e8-ba15-15788c6d3a29

import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_Representable
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Shared_IsExtremeSupport
import Theorems.Thm_WeylPolyhedra_Pyramid_hauptsatz

-- carved verbatim out of submission b2ce9b3d-1e4e-438b-98b8-5f7a2c12ec36, lines 438-442

section
open WeylPolyhedra
open Matrix Module

lemma wp_cara {n : ℕ} (x : Fin n → ℝ) : ∀ (k : ℕ) (S : Finset (Fin n → ℝ)), S.card = k →
    Shared.Representable S x →
    ∃ T ⊆ S, LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)) ∧ Shared.Representable T x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro S hk ⟨c, hc0, hx⟩
  by_cases hli : LinearIndependent ℝ (fun t : S => (t : Fin n → ℝ))
  · exact ⟨S, subset_rfl, hli, c, hc0, hx⟩
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
  classical
  let G : (Fin n → ℝ) → ℝ := fun v => if h : v ∈ S then g ⟨v, h⟩ else 0
  have hG : ∑ s ∈ S, G s • s = 0 := by
    rw [← hg, ← Finset.sum_coe_sort S]
    exact Finset.sum_congr rfl fun s _ => by simp [G, s.2]
  have hGi : G i ≠ 0 := by simpa [G, i.2] using hi
  obtain ⟨H, hH, s1, hs1, hpos⟩ : ∃ H : (Fin n → ℝ) → ℝ, ∑ s ∈ S, H s • s = 0 ∧
      ∃ s1 ∈ S, 0 < H s1 := by
    rcases lt_or_gt_of_ne hGi with h | h
    · refine ⟨fun v => - G v, ?_, i, i.2, by simp; linarith⟩
      simp [neg_smul, Finset.sum_neg_distrib, hG]
    · exact ⟨G, hG, i, i.2, h⟩
  let P := S.filter (fun s => 0 < H s)
  obtain ⟨s0, hs0P, hmin⟩ := P.exists_min_image (fun s => c s / H s)
    ⟨s1, by simp [P, hs1, hpos]⟩
  have hs0 : s0 ∈ S ∧ 0 < H s0 := by simpa [P] using hs0P
  set t := c s0 / H s0 with ht
  have ht0 : 0 ≤ t := div_nonneg (hc0 s0 hs0.1) hs0.2.le
  let c' : (Fin n → ℝ) → ℝ := fun s => c s - t * H s
  have hc' : ∀ s ∈ S, 0 ≤ c' s := by
    intro s hs
    by_cases hHs : 0 < H s
    · have := hmin s (by simp [P, hs, hHs])
      rw [le_div_iff₀ hHs] at this
      simp only [c']; linarith
    · push_neg at hHs
      have := hc0 s hs
      simp only [c']; nlinarith
  have hc's0 : c' s0 = 0 := by
    simp only [c', t]; rw [div_mul_cancel₀ _ hs0.2.ne']; ring
  have hx' : x = ∑ s ∈ S.erase s0, c' s • s := by
    rw [Finset.sum_erase S (by simp [hc's0])]
    simp only [c', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hH, hx]
    simp
  obtain ⟨T, hTS, hTli, hTr⟩ := ih _ (by rw [← hk]; exact Finset.card_erase_lt_of_mem hs0.1)
    (S.erase s0) rfl ⟨c', fun s hs => hc' s (Finset.mem_of_mem_erase hs), hx'⟩
  exact ⟨T, hTS.trans (Finset.erase_subset _ _), hTli, hTr⟩

theorem hauptsatz_n_core {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (x : Fin n → ℝ) (hx : ∀ α : Fin n → ℝ, Shared.IsExtremeSupport S α → 0 ≤ α ⬝ᵥ x) :
    ∃ T : Finset (Fin n → ℝ), T ⊆ S ∧ T.card ≤ n ∧ Shared.Representable T x := by
  obtain ⟨T, hTS, hli, hr⟩ := wp_cara x _ S rfl (WeylPolyhedra.Pyramid.hauptsatz S hS x hx)
  refine ⟨T, hTS, ?_, hr⟩
  have := hli.finset_card_le_finrank
  simpa [Module.finrank_fin_fun] using this

end

section
open WeylPolyhedra

theorem solution {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (x : Fin n → ℝ) (hx : ∀ α : Fin n → ℝ, Shared.IsExtremeSupport S α → 0 ≤ α ⬝ᵥ x) :
    ∃ T : Finset (Fin n → ℝ), T ⊆ S ∧ T.card ≤ n ∧ Shared.Representable T x := by
  exact hauptsatz_n_core S hS x hx

end
