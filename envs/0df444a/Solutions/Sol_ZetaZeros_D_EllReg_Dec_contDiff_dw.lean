-- Prove2me | solution 1 for ZetaZeros.D.EllReg.Dec.contDiff_dw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:57.10595+00:00
-- url     : https://prove2.me/submissions/822a9760-8e63-476b-bed8-65e97902a3cf

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_Decompose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
open ZetaZeros.D.EllReg.Dec
variable {d : ℕ}
namespace ZetaZeros.D.EllReg.Dec
theorem _root_.solution {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) (w : List (Fin d)) : ContDiff ℝ ∞ (dw w f) := by
  induction w with
  | nil => exact hf
  | cons j w ih =>
    show ContDiff ℝ ∞ (fun x => fderiv ℝ (dw w f) x (ev j))
    exact (contDiff_infty_iff_fderiv.mp ih).2.clm_apply contDiff_const
end ZetaZeros.D.EllReg.Dec
