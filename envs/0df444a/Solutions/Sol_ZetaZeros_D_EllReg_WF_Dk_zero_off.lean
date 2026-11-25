-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WF.Dk_zero_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:11:52.567249+00:00
-- url     : https://prove2.me/submissions/44b8c0e0-9046-471d-b6af-e21b5058fc21

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
theorem _root_.solution {f : E d → ℂ} {K : Set (E d)} (hK : IsClosed K) (hf : ∀ y ∉ K, f y = 0) (k : Fin d) :
    ∀ y ∉ K, Dk k f y = 0 := by
  intro y hy
  have h : f =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hy] with z hz
    exact hf z hz
  show fderiv ℝ f y (ZetaZeros.D.EllReg.ev k) = 0
  rw [h.fderiv_eq]
  simp
end ZetaZeros.D.EllReg.WF
