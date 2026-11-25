-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WF.smooth_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:03:35.409974+00:00
-- url     : https://prove2.me/submissions/58b6d256-dc48-4882-919b-6684c2f2e292

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
theorem _root_.solution {U : Set (E d)} (hU : IsOpen U) {a : E d → ℂ} (ha : ContDiffOn ℝ ∞ a U)
    {χ : E d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U) :
    ContDiff ℝ ∞ (fun y => (χ y : ℂ) * a y) := by
  have hz0 : ∀ z, z ∉ tsupport χ → χ z = 0 := fun z hz => by
    by_contra h
    exact hz (subset_tsupport χ (Function.mem_support.mpr h))
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (contDiff_ofReal' hχ).contDiffAt.mul (ha.contDiffAt (hU.mem_nhds hx))
  · have hxs : x ∉ tsupport χ := fun h => hx (hχU h)
    have hev : (fun y => (χ y : ℂ) * a y) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxs] with z hz
      simp [hz0 z hz]
    exact contDiffAt_const.congr_of_eventuallyEq hev
end ZetaZeros.D.EllReg.WF
