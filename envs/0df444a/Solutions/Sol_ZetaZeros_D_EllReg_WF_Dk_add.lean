-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WF.Dk_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:37.218301+00:00
-- url     : https://prove2.me/submissions/43b2993f-bdce-4959-92a8-831069415bf0

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
private theorem differentiable_of_contDiff'_lemma {f : ZetaZeros.D.EllReg.E d → ℂ} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f := by
  exact (contDiff_infty_iff_fderiv.mp hf).1
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
theorem _root_.solution {f g : E d → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : Fin d) (y : E d) :
    Dk k (fun z => f z + g z) y = Dk k f y + Dk k g y := by
  have H := ((differentiable_of_contDiff'_lemma hf y).hasFDerivAt.add (differentiable_of_contDiff'_lemma hg y).hasFDerivAt).fderiv
  show fderiv ℝ (f + g) y (ZetaZeros.D.EllReg.ev k) = fderiv ℝ f y (ZetaZeros.D.EllReg.ev k) + fderiv ℝ g y (ZetaZeros.D.EllReg.ev k)
  rw [H]
  rfl
end ZetaZeros.D.EllReg.WF
