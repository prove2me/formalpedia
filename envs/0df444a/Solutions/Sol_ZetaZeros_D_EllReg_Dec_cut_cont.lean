-- Prove2me | solution 1 for ZetaZeros.D.EllReg.Dec.cut_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:17:29.776716+00:00
-- url     : https://prove2.me/submissions/8ec52325-eb36-4db9-b094-b7f3d03f4d0b

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
theorem _root_.solution {U : Set (E d)} (hU : IsOpen U) {u : E d → ℂ} (hu : ContinuousOn u U) {χ : E d → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    Continuous (cut χ u) ∧ HasCompactSupport (cut χ u) := by
  have hχU' : ∀ x, x ∉ U → cut χ u =ᶠ[𝓝 x] 0 := by
    intro x hx
    have hx' : x ∉ tsupport χ := fun h => hx (hχU h)
    have hev : χ =ᶠ[𝓝 x] 0 := by
      first
        | exact notMem_tsupport_iff_eventuallyEq.mp hx'
        | exact not_mem_tsupport_iff_eventuallyEq.mp hx'
    filter_upwards [hev] with y hy
    simp [cut, hy]
  refine ⟨continuous_iff_continuousAt.mpr fun x => ?_, ?_⟩
  · by_cases hx : x ∈ U
    · exact (Complex.continuous_ofReal.comp hχ.continuous).continuousAt.mul
        (hu.continuousAt (hU.mem_nhds hx))
    · exact continuousAt_const.congr (hχU' x hx).symm
  · exact (hχc.comp_left Complex.ofReal_zero).mul_right
end ZetaZeros.D.EllReg.Dec
