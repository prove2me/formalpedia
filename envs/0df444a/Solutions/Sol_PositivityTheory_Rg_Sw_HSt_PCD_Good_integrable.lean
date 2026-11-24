-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.PCD.Good.integrable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:28.616804+00:00
-- url     : https://prove2.me/submissions/1154437d-2dfa-4b85-8965-d0b234513550

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_ParamCD
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_PCD_Good_continuousOn

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
namespace Good
theorem _root_.solution (hK : Good Ω K) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] {x : F} (hx : x ∈ Ω) :
    Integrable (K x) ν := by
  obtain ⟨V, -, hxV, C, hC, hKV⟩ := hK.supp x hx
  have hc : Continuous (K x) := by
    have := hK.continuousOn
    exact this.comp_continuous (Continuous.prodMk continuous_const continuous_id) (fun u => ⟨hx, mem_univ _⟩)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.intro hC fun u hu => hKV x hxV u hu)
end Good
end PositivityTheory.Rg.Sw.HSt.PCD
