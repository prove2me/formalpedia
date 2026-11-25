-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WF.intg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:18:06.305839+00:00
-- url     : https://prove2.me/submissions/a6cb6714-5dfc-4cc3-9e61-665de556be32

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
theorem _root_.solution {U K : Set (E d)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) {u F : E d → ℂ}
    (hu : ContinuousOn u U) (hF : Continuous F) (hFK : ∀ y ∉ K, F y = 0) :
    Integrable (fun y => u y * F y) := by
  have hKc : IsClosed K := hK.isClosed
  have hcont : Continuous (fun y => u y * F y) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hu.continuousAt (hU.mem_nhds hx)).mul hF.continuousAt
    · have hxK : x ∉ K := fun h => hx (hKU h)
      have hev : (fun _ => (0 : ℂ)) =ᶠ[𝓝 x] fun y => u y * F y := by
        filter_upwards [hKc.isOpen_compl.mem_nhds hxK] with z hz
        simp [hFK z hz]
      exact continuousAt_const.congr hev
  have hcs : HasCompactSupport (fun y => u y * F y) := by
    apply HasCompactSupport.intro hK
    intro y hy
    simp [hFK y hy]
  exact hcont.integrable_of_hasCompactSupport hcs
end ZetaZeros.D.EllReg.WF
