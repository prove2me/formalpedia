-- Prove2me | solution 1 for PI.FJMP.pureJ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:05:41.936132+00:00
-- url     : https://prove2.me/submissions/9a457f9c-fa4b-40d5-a42d-d0f81ef96c49

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Theorems.Thm_PI_FJMP_pure_gen
import Theorems.Thm_PI_FJMP_monomialLeftWeight_eq_weight_sub
import Theorems.Thm_PI_FJMP_monomialRightWeight_eq_weight_sub
import Theorems.Thm_PI_FJMP_mem_leftHighestWeight_of_isMinimalJointVector
import Theorems.Thm_PI_FJMP_mem_rightHighestWeight_of_isMinimalJointVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMP
open PI.FJM
namespace PI.FJMP
theorem _root_.solution (hW1 : FormWt1) (hW2 : FormWt2) : PureJ := by
  intro p q r s μ μ' P hM e he l hl
  have hP1 := mem_leftHighestWeight_of_isMinimalJointVector hM
  have hP2 := mem_rightHighestWeight_of_isMinimalJointVector hM
  have hM' := hM
  unfold MinHyp at hM'
  obtain ⟨-, -, d, hd1, hd2, hH⟩ := hM'
  have hdeg : ∑ l : Ln p q r s, e l = d := by
    have h0 := (mem_homogeneousSubmodule d P).mp hH (mem_support_iff.mp he)
    first
      | simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using h0
      | simpa [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum] using h0
  have hsum : (∑ a : Ix p q, ∑ c : Ix r s, (e (a, c) : ℤ)) = d := by
    rw [← Fintype.sum_prod_type']
    exact_mod_cast hdeg
  have hrow : ∑ a, |∑ c : Ix r s, (if linePos ((a, c) : Ln p q r s) = true then (e (a, c) : ℤ) else -(e (a, c) : ℤ))|
      = ∑ a : Ix p q, ∑ c : Ix r s, (e (a, c) : ℤ) := by
    have h1 : (∑ a, |((wt1 e a : ℤ) : ℚ)|) = (d : ℚ) := by
      rw [hd1]
      unfold degW
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [monomialLeftWeight_eq_weight_sub hW1 hP1 e he a]
    have h3 : (∑ a, |wt1 e a|) = (d : ℤ) := by exact_mod_cast h1
    rw [hsum]
    exact h3
  have hcol : ∑ c, |∑ a : Ix p q, (if linePos ((a, c) : Ln p q r s) = true then (e (a, c) : ℤ) else -(e (a, c) : ℤ))|
      = ∑ c : Ix r s, ∑ a : Ix p q, (e (a, c) : ℤ) := by
    have h1 : (∑ c, |((wt2 e c : ℤ) : ℚ)|) = (d : ℚ) := by
      rw [hd2]
      unfold degW
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [monomialRightWeight_eq_weight_sub hW2 hP2 e he c]
    have h3 : (∑ c, |wt2 e c|) = (d : ℤ) := by exact_mod_cast h1
    rw [Finset.sum_comm, hsum]
    exact h3
  obtain ⟨a, c⟩ := l
  obtain ⟨r1, r2⟩ := pure_gen (fun a c => (e ((a, c) : Ln p q r s))) (fun a c => linePos ((a, c) : Ln p q r s))
    hrow a c hl
  obtain ⟨c1, c2⟩ := pure_gen (fun c a => (e ((a, c) : Ln p q r s))) (fun c a => linePos ((a, c) : Ln p q r s))
    hcol c a hl
  have r1' : wt1 e a ≠ 0 := r1
  have r2' : linePos ((a, c) : Ln p q r s) = true ↔ 0 < wt1 e a := r2
  have c1' : wt2 e c ≠ 0 := c1
  have c2' : linePos ((a, c) : Ln p q r s) = true ↔ 0 < wt2 e c := c2
  have hw1 := monomialLeftWeight_eq_weight_sub hW1 hP1 e he a
  have hw2 := monomialRightWeight_eq_weight_sub hW2 hP2 e he c
  have k1 : nu1 p q r s μ a ≠ 0 := by
    rw [← hw1]
    exact_mod_cast r1'
  have k2 : nu2 p q r s μ' c ≠ 0 := by
    rw [← hw2]
    exact_mod_cast c1'
  have k3 : linePos ((a, c) : Ln p q r s) = true ↔ 0 < nu1 p q r s μ a := by
    rw [← hw1, r2']
    exact Int.cast_pos.symm
  have k4 : linePos ((a, c) : Ln p q r s) = true ↔ 0 < nu2 p q r s μ' c := by
    rw [← hw2, c2']
    exact Int.cast_pos.symm
  exact ⟨k1, k2, k3, k4⟩
end PI.FJMP
