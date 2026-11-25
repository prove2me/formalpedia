-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.contraction_first_operator_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:16.759378+00:00
-- url     : https://prove2.me/submissions/09052c7f-488a-4b6e-bbc8-2b2d9d0aa444

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ContractionFirstOperatorAdjoint
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_tA
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_tB
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_tC
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_tD
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_contr_neg
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_contr_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_contr_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_pE
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
theorem _root_.solution (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (a b : Fin m) {h g : PX m n} (hh : h ∈ F1 ε)
    (hg : g ∈ F2 ε) : contr c (D1 ε c a b h * g) = -contr c (h * D2 ε c a b g) := by
  have hc2 : ((2 * c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * c) ≠ 0)
  unfold D1 D2
  by_cases hab : ε a = ε b
  · rw [if_pos hab, if_pos hab]
    cases ha : ε a
    · have hb : ε b = false := by rw [← hab, ha]
      simp only [Bool.false_eq_true, if_false]
      rw [Finset.sum_mul, contr_sum, mul_neg, contr_neg, Finset.mul_sum, contr_sum, neg_neg]
      exact Finset.sum_congr rfl fun i _ => tB ε hc ha hb i hh hg
    · have hb : ε b = true := by rw [← hab, ha]
      simp only [if_true]
      rw [neg_mul, contr_neg, Finset.sum_mul, contr_sum, Finset.mul_sum, contr_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => tA ε hc ha hb i hh hg
  · rw [if_neg hab, if_neg hab]
    cases ha : ε a
    · have hb : ε b = true := by cases h' : ε b <;> simp_all
      simp only [Bool.false_eq_true, if_false]
      rw [smul_mul_assoc, contr_smul, Finset.sum_mul, contr_sum, mul_smul_comm, contr_smul, Finset.mul_sum _ _ h,
        contr_sum]
      simp_rw [← tD ε hc ha hb _ hh hg]
      rw [← Finset.mul_sum]
      push_cast at hc2 ⊢
      field_simp
    · have hb : ε b = false := by cases h' : ε b <;> simp_all
      simp only [if_true]
      rw [smul_mul_assoc, contr_smul, Finset.sum_mul, contr_sum, mul_smul_comm, contr_smul, Finset.mul_sum _ _ h,
        contr_sum]
      simp_rw [tC ε hc ha hb _ hh hg]
      rw [← Finset.mul_sum]
      push_cast at hc2 ⊢
      field_simp
end PositivityTheory.Rg.Sw.LC.CoreC
