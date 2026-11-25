-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_HSt_PCD_contDiffOn_integral__5b3d1c8257c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:57:32.216799+00:00
-- url     : https://prove2.me/submissions/b87f0231-850c-41dd-961d-ef1dbd3ca7e9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_ParamCD
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_PCD_contDiffOn_integral
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_PCD_good_of_joint

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {Ω : Set F}
namespace PositivityTheory.Rg.Sw.HSt.PCD
theorem _root_.solution (hΩ : IsOpen Ω) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (k : F × V → E)
    (hk : ContDiffOn ℝ ∞ k (Ω ×ˢ univ)) (v : X → V) (hv : Continuous v) (h : X → ℂ) (hh : Continuous h)
    (hsupp : ∀ x ∈ Ω, ∃ W ∈ 𝓝 x, ∃ C : Set X, IsCompact C ∧ ∀ x' ∈ W, ∀ u ∉ C, k (x', v u) = 0) :
    ContDiffOn ℝ ∞ (fun x => ∫ u, h u • k (x, v u) ∂ν) Ω :=
  contDiffOn_integral hΩ ν (good_of_joint hΩ k hk v hv h hh hsupp)
end PositivityTheory.Rg.Sw.HSt.PCD
