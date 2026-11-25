-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.PCD.contDiffOn_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:47:34.333797+00:00
-- url     : https://prove2.me/submissions/3985ead6-9d34-4ad1-b3e4-bff29b4ea58d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_ParamCD
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_PCD_contDiffOn_nat

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
    (hK : Good Ω K) : ContDiffOn ℝ ∞ (fun x => ∫ u, K x u ∂ν) Ω :=
  contDiffOn_infty.2 fun N => contDiffOn_nat hΩ ν N E K hK
end PositivityTheory.Rg.Sw.HSt.PCD
