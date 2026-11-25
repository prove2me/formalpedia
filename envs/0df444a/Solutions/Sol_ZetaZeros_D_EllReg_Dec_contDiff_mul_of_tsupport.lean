-- Prove2me | solution 1 for ZetaZeros.D.EllReg.Dec.contDiff_mul_of_tsupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:17:27.47809+00:00
-- url     : https://prove2.me/submissions/0398e7c8-0e64-45f6-9b27-d909f126e695

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
theorem _root_.solution {U : Set (E d)} (hU : IsOpen U) {g f : E d → ℂ} (hg : ContDiff ℝ ∞ g)
    (hgU : tsupport g ⊆ U) (hf : ContDiffOn ℝ ∞ f U) : ContDiff ℝ ∞ (fun x => g x * f x) := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  by_cases hx : x ∈ U
  · exact hg.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport g := fun h => hx (hgU h)
    have hev : g =ᶠ[𝓝 x] 0 := by
      first
        | exact notMem_tsupport_iff_eventuallyEq.mp hx'
        | exact not_mem_tsupport_iff_eventuallyEq.mp hx'
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with y hy
    simp [hy]
end ZetaZeros.D.EllReg.Dec
