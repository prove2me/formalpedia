-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.NullS.norm_crd_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:38.797295+00:00
-- url     : https://prove2.me/submissions/c3546071-122b-4312-bb12-98f726453c9f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HasFDerivAtEvX
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_crd_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.NullS
theorem _root_.solution (k : Fin m × Fin n × Bool) (x : Fin m → Fin n → ℂ) : ‖crd k x‖ ≤ ‖x‖ := by
  rw [crd_apply]
  have h : ‖x k.1 k.2.1‖ ≤ ‖x‖ := (norm_le_pi_norm (x k.1) k.2.1).trans (norm_le_pi_norm x k.1)
  split_ifs <;> simpa using h
end PositivityTheory.Rg.Sw.LC.NullS
