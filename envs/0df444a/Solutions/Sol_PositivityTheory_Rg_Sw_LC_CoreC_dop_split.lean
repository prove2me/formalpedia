-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.dop_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:54:28.870709+00:00
-- url     : https://prove2.me/submissions/88d0ae9d-d2de-49a6-8076-e6faa9858a56

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ContractionFirstOperatorAdjoint
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_XPderivMono
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_pE
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_partial_deriv_zero_first_family
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_partial_deriv_zero_second_family
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LC.CoreC.pE_apply
attribute [local simp] PositivityTheory.Rg.Sw.LC.CoreC.pE_pE



set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreC
theorem _root_.solution (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) {f g : PX m n} (hf : f ∈ F1 ε) (hg : g ∈ F2 ε) :
    Dop ε c a b (f * g) = D1 ε c a b f * g + f * D2 ε c a b g := by
  have hL : ∀ k, pderiv k (f * g) = f * pderiv k g + g * pderiv k f := fun k => by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have hL2 : ∀ k (p q : PX m n), pderiv k (p * q) = p * pderiv k q + q * pderiv k p := fun k p q => by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  unfold Dop D1 D2
  by_cases hab : ε a = ε b
  · rw [if_pos hab, if_pos hab, if_pos hab]
    cases ha : ε a
    · have hb : ε b = false := by rw [← hab, ha]
      simp only [Bool.false_eq_true, if_false]
      simp only [Finset.sum_mul, Finset.mul_sum, neg_mul, mul_neg, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hL, hL, partial_deriv_zero_second_family ε (k := (a, i, true)) (by simp [inF1, ha]) hg,
        partial_deriv_zero_first_family ε (k := (b, i, false)) (by simp [inF1, hb]) hf]
      ring
    · have hb : ε b = true := by rw [← hab, ha]
      simp only [if_true]
      simp only [Finset.sum_mul, Finset.mul_sum, neg_mul, mul_neg, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hL, hL, partial_deriv_zero_first_family ε (k := (a, i, true)) (by simp [inF1, ha]) hf,
        partial_deriv_zero_second_family ε (k := (b, i, false)) (by simp [inF1, hb]) hg]
      ring
  · rw [if_neg hab, if_neg hab, if_neg hab]
    cases ha : ε a
    · have hb : ε b = true := by cases h' : ε b <;> simp_all
      simp only [Bool.false_eq_true, if_false]
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Finset.smul_sum, neg_mul, mul_neg,
        neg_smul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hL, map_add, hL2 _ f, hL2 _ g, partial_deriv_zero_second_family ε (k := (a, i, true)) (by simp [inF1, ha]) hg,
        partial_deriv_zero_second_family ε (k := (b, i, false)) (by simp [inF1, hb]) hg]
      simp only [mul_zero, zero_add, add_zero, zero_mul, map_zero, smul_eq_C_mul]
      ring
    · have hb : ε b = false := by cases h' : ε b <;> simp_all
      simp only [if_true]
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Finset.smul_sum, neg_mul, mul_neg,
        neg_smul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hL, partial_deriv_zero_first_family ε (k := (a, i, true)) (by simp [inF1, ha]) hf, mul_zero, add_zero, hL2 _ f,
        partial_deriv_zero_first_family ε (k := (b, i, false)) (by simp [inF1, hb]) hf, mul_zero, add_zero]
      simp only [smul_eq_C_mul]
      ring
end PositivityTheory.Rg.Sw.LC.CoreC
