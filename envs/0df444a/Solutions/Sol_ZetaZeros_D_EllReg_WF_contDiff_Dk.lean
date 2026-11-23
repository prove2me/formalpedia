-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WF.contDiff_Dk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:37.903113+00:00
-- url     : https://prove2.me/submissions/7510328c-79a7-4205-9888-4be64f7d18a3

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
namespace WF
variable {d : ℕ}
private theorem contDiff_fderiv'_lemma_2 {f : ZetaZeros.D.EllReg.E d → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fderiv ℝ f) := by
  exact (contDiff_infty_iff_fderiv.mp hf).2
end WF
end
end ZetaZeros.D.EllReg
end

set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
open ZetaZeros.D.EllReg.WF
variable {d : ℕ}
namespace ZetaZeros.D.EllReg.WF
theorem _root_.solution {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) (k : Fin d) : ContDiff ℝ ∞ (Dk k f) := by
  exact (contDiff_fderiv'_lemma_2 hf).clm_apply contDiff_const
end ZetaZeros.D.EllReg.WF
