-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.line_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:50.620812+00:00
-- url     : https://prove2.me/submissions/235f5ddb-54f5-431d-93cc-8c0ee4462cbf

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution {F : E n → ℂ} {y : E n} (hF : DifferentiableAt ℝ F y) (h : E n) :
    HasDerivAt (fun t : ℝ => F (y + t • h)) (fderiv ℝ F y h) 0 := by
  have hl : HasDerivAt (fun t : ℝ => y + t • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add y
  have hF' : HasFDerivAt F (fderiv ℝ F y) (y + (0 : ℝ) • h) := by simpa using hF.hasFDerivAt
  exact hF'.comp_hasDerivAt (0 : ℝ) hl
end PositivityTheory.Rg.Sw.WR.B
