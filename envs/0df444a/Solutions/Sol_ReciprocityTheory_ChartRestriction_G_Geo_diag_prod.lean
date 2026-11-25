-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.diag_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:10.269227+00:00
-- url     : https://prove2.me/submissions/a2be7f92-c79d-43bf-8d74-c4339dadcc3f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (d : ℕ) : ∀ e : (Σ k, ι k) → ℕ, (∀ k, ∑ i, e ⟨k, i⟩ = d) →
    ∃ G : MvPolynomial ((k : K) → ι k) ℂ, G.totalDegree ≤ d ∧
      ∀ z : (Σ k, ι k) → ℂ, ∏ p, z p ^ e p = eval (segre z) G := by
  induction d with
  | zero =>
    intro e he
    refine ⟨1, by simp, fun z => ?_⟩
    have h0 : ∀ p, e p = 0 := by
      intro p
      have := he p.1
      rw [Finset.sum_eq_zero_iff] at this
      exact this p.2 (Finset.mem_univ _)
    simp [h0]
  | succ d ih =>
    intro e he
    have hex : ∀ k, ∃ i, 0 < e ⟨k, i⟩ := by
      intro k
      by_contra hne
      push_neg at hne
      have h1 := he k
      rw [Finset.sum_eq_zero (fun i _ => Nat.le_zero.1 (hne i))] at h1
      omega
    choose i0 hi0 using hex
    classical
    let e' : (Σ k, ι k) → ℕ := fun p => if p.2 = i0 p.1 then e p - 1 else e p
    have hblk : ∀ k, ∑ i, e' ⟨k, i⟩ = d := by
      intro k
      have h1 := he k
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (i0 k))] at h1 ⊢
      have h2 : ∑ i ∈ Finset.univ.erase (i0 k), e' ⟨k, i⟩ = ∑ i ∈ Finset.univ.erase (i0 k), e ⟨k, i⟩ := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hne : i ≠ i0 k := Finset.ne_of_mem_erase hi
        simp [e', hne]
      rw [h2]
      have h3 : e' ⟨k, i0 k⟩ = e ⟨k, i0 k⟩ - 1 := by simp [e']
      rw [h3]
      have := hi0 k
      omega
    obtain ⟨G', hG'deg, hG'⟩ := ih e' hblk
    refine ⟨X i0 * G', ?_, fun z => ?_⟩
    · calc (X i0 * G').totalDegree ≤ (X i0 : MvPolynomial ((k : K) → ι k) ℂ).totalDegree + G'.totalDegree :=
            totalDegree_mul _ _
        _ ≤ 1 + d := by rw [totalDegree_X]; omega
        _ = d + 1 := by ring
    · rw [eval_mul, eval_X, ← hG', segre, Fintype.prod_sigma, Fintype.prod_sigma, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (i0 k)),
        ← Finset.mul_prod_erase _ _ (Finset.mem_univ (i0 k))]
      have h2 : ∏ i ∈ Finset.univ.erase (i0 k), z ⟨k, i⟩ ^ e' ⟨k, i⟩ =
          ∏ i ∈ Finset.univ.erase (i0 k), z ⟨k, i⟩ ^ e ⟨k, i⟩ := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have hne : i ≠ i0 k := Finset.ne_of_mem_erase hi
        simp [e', hne]
      rw [h2]
      have h3 : e' ⟨k, i0 k⟩ = e ⟨k, i0 k⟩ - 1 := by simp [e']
      rw [h3]
      have h4 : e ⟨k, i0 k⟩ = e ⟨k, i0 k⟩ - 1 + 1 := by have := hi0 k; omega
      conv_lhs => rw [h4, pow_succ]
      ring
end ReciprocityTheory.ChartRestriction.G.Geo
