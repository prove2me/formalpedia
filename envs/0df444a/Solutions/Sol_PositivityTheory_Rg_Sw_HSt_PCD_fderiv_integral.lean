-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.PCD.fderiv_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:23:41.107195+00:00
-- url     : https://prove2.me/submissions/0197053d-2c44-4cc1-8a34-7253b4e26e3b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_ParamCD
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_PCD_Good_hasFDerivAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.PCD
variable {F X : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X] [SecondCountableTopology X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set F} {K : F → X → E}
namespace PositivityTheory.Rg.Sw.HSt.PCD
theorem _root_.solution [CompleteSpace E] (hΩ : IsOpen Ω) (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    (hK : Good Ω K) {x : F} (hx : x ∈ Ω) :
    fderiv ℝ (fun x => ∫ u, K x u ∂ν) x = ∫ u, fderiv ℝ (K · u) x ∂ν :=
  (hK.hasFDerivAt hΩ ν hx).fderiv
end PositivityTheory.Rg.Sw.HSt.PCD
