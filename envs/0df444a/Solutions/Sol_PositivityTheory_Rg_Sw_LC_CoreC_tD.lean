-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.tD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:17:49.763464+00:00
-- url     : https://prove2.me/submissions/c8352891-68c8-4d8c-9946-31b51b1a47cf

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ContractionFirstOperatorAdjoint
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_T2
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_pE
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_partial_deriv_mem_first_family
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_variable_mul_mem_second_family
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
theorem _root_.solution (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {a b : Fin m} (ha : ε a = false) (hb : ε b = true) (i : Fin n)
    {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    ((2 * c : ℝ) : ℂ) ^ 2 * contr c (pderiv (b, i, false) (pderiv (a, i, true) h) * g) =
      contr c (h * (X (a, i, false) * X (b, i, true) * g)) := by
  have hbT : ¬ inF1 ε (b, i, true) := by simp [inF1, hb]
  have h1 := T2 ε (c := c) (k := (b, i, false)) (by simp [inF1, hb]) (partial_deriv_mem_first_family ε (a, i, true) hh) hg
  have h2 := T2 ε (c := c) (k := (a, i, true)) (by simp [inF1, ha]) hh (variable_mul_mem_second_family ε hbT hg)
  simp only [pE_apply, Bool.not_false, Bool.not_true] at h1 h2
  rw [pow_two, mul_assoc, h1, h2, mul_assoc]
end PositivityTheory.Rg.Sw.LC.CoreC
