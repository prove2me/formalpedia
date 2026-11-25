-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WF.contDiff_eF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:18:54.118871+00:00
-- url     : https://prove2.me/submissions/a37495fe-2283-48be-9c7a-c789236ca020

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier
import Theorems.Thm_P2M_ZetaZeros_D_EllReg_WF_contDiff_ofReal__ad18da8cd330

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
open ZetaZeros.D.EllReg.WF
variable {d : ℕ}
namespace ZetaZeros.D.EllReg.WF
theorem _root_.solution (ξ : E d) : ContDiff ℝ ∞ (eF ξ) := by
  have h1 : ContDiff ℝ ∞ (fun y : ZetaZeros.D.EllReg.E d => (inner ℝ y ξ : ℝ)) := by
    exact contDiff_id.inner ℝ contDiff_const
  have h2 := contDiff_ofReal' h1
  have h3 : ContDiff ℝ ∞ (fun y : ZetaZeros.D.EllReg.E d => -(2 * Real.pi * Complex.I * ((inner ℝ y ξ : ℝ) : ℂ))) :=
    (contDiff_const.mul h2).neg
  exact h3.cexp
end ZetaZeros.D.EllReg.WF
