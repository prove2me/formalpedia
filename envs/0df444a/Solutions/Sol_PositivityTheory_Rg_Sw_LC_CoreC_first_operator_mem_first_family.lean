-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.first_operator_mem_first_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:42:09.834526+00:00
-- url     : https://prove2.me/submissions/6eb51ffe-7ca4-4cff-a462-3ec19760e17d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FunctionalRepresentationByContraction
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SecondOperatorMemSecondFamily
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_pE
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_partial_deriv_mem_first_family
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_variable_mul_mem_first_family
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
theorem _root_.solution (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) {f : PX m n} (hf : f ∈ F1 ε) : D1 ε c a b f ∈ F1 ε := by
  unfold D1
  split_ifs with hab ha ha
  · refine (F1 ε).neg_mem ((F1 ε).sum_mem fun i _ => variable_mul_mem_first_family ε (by simp [inF1, ha]) (partial_deriv_mem_first_family ε _ hf))
  · exact (F1 ε).sum_mem fun i _ => variable_mul_mem_first_family ε (by simp [inF1, ← hab]; simpa using ha) (partial_deriv_mem_first_family ε _ hf)
  · have hb : ε b = false := by cases h' : ε b <;> simp_all
    refine (F1 ε).smul_mem _ ((F1 ε).sum_mem fun i _ => ?_)
    rw [mul_assoc]
    exact variable_mul_mem_first_family ε (by simp [inF1, ha]) (variable_mul_mem_first_family ε (by simp [inF1, hb]) hf)
  · have hb : ε b = true := by cases h' : ε b <;> simp_all
    exact (F1 ε).smul_mem _ ((F1 ε).sum_mem fun i _ => partial_deriv_mem_first_family ε _ (partial_deriv_mem_first_family ε _ hf))
end PositivityTheory.Rg.Sw.LC.CoreC
