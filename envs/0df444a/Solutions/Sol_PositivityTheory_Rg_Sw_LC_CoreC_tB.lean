-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.tB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:17:43.409876+00:00
-- url     : https://prove2.me/submissions/3220ad17-5715-49f6-822d-3c3d2b676d2f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ContractionFirstOperatorAdjoint
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_T1
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_T2
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_pE
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_partial_deriv_mem_first_family
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_partial_deriv_mem_second_family
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
theorem _root_.solution (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {a b : Fin m} (ha : ε a = false) (hb : ε b = false) (i : Fin n)
    {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (X (b, i, true) * pderiv (a, i, true) h * g) = contr c (h * (X (a, i, false) * pderiv (b, i, false) g)) := by
  have h1 := T1 ε (c := c) (k := (b, i, true)) (by simp [inF1, hb]) (partial_deriv_mem_first_family ε (a, i, true) hh) hg
  have h2 := T2 ε (c := c) (k := (a, i, true)) (by simp [inF1, ha]) hh (partial_deriv_mem_second_family ε (b, i, false) hg)
  simp only [pE_apply, Bool.not_true] at h1 h2
  rw [h1, h2]
end PositivityTheory.Rg.Sw.LC.CoreC
