-- Prove2me | solution 1 for P2M_ZetaZeros_D_EllReg_WF_contDiff_ofReal__ad18da8cd330
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:07.924531+00:00
-- url     : https://prove2.me/submissions/38d18ae6-9e66-49b5-836b-b403b0706930

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier

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
theorem _root_.solution {χ : E d → ℝ} (hχ : ContDiff ℝ ∞ χ) : ContDiff ℝ ∞ (fun y => (χ y : ℂ)) := by
  have h := Complex.ofRealCLM.contDiff.comp hχ
  have e : (Complex.ofRealCLM ∘ χ) = fun y => (χ y : ℂ) := by
    funext y; simp
  rw [e] at h
  exact h
end ZetaZeros.D.EllReg.WF
