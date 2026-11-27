-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_HSt_PCD_hasFDerivAt_integral__c09389d3d1db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:14:26.876469+00:00
-- url     : https://prove2.me/submissions/ee3ba97c-0352-43ca-847e-a8a8ede58e39

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_ParamCD
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_PCD_Good_hasFDerivAt
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
    (hsupp : ∀ x ∈ Ω, ∃ W ∈ 𝓝 x, ∃ C : Set X, IsCompact C ∧ ∀ x' ∈ W, ∀ u ∉ C, k (x', v u) = 0) {x : F} (hx : x ∈ Ω) :
    HasFDerivAt (fun x => ∫ u, h u • k (x, v u) ∂ν) (∫ u, h u • fderiv ℝ (fun x' => k (x', v u)) x ∂ν) x := by
  have hG := good_of_joint hΩ k hk v hv h hh hsupp
  have := hG.hasFDerivAt hΩ ν hx
  convert this using 2
  funext u
  have hsl : ContDiffOn ℝ ∞ (fun x => k (x, v u)) Ω :=
    hk.comp (contDiffOn_id.prodMk contDiffOn_const) fun x hx => ⟨hx, mem_univ _⟩
  have hd : DifferentiableAt ℝ (fun x => k (x, v u)) x :=
    (hsl.differentiableOn (by simp) x hx).differentiableAt (hΩ.mem_nhds hx)
  exact ((hd.hasFDerivAt.const_smul (h u)).fderiv).symm
end PositivityTheory.Rg.Sw.HSt.PCD
