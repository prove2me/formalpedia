-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.extend_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:28:01.19227+00:00
-- url     : https://prove2.me/submissions/9599b558-d120-4b70-86ca-0e9351c2ed0c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Extend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (G : V n → ℂ) (he : IsChart n z e)
    (he' : IsChart n z e') (y : V n) (hy : y ∈ e'.target) (hs : e'.symm y ∈ e.source) :
    (e.source.indicator (G ∘ e) ∘ e'.symm) =ᶠ[𝓝 y] G := by
  have hopen : IsOpen (e'.target ∩ e'.symm ⁻¹' e.source) :=
    e'.isOpen_inter_preimage_symm e.open_source
  filter_upwards [hopen.mem_nhds ⟨hy, hs⟩] with w hw
  obtain ⟨hw1, hw2⟩ := hw
  have hw3 : e'.symm w ∈ e'.source := e'.map_target hw1
  rw [Function.comp_apply, Set.indicator_of_mem (show e'.symm w ∈ e.source from hw2), Function.comp_apply, ← he hw2, he' hw3,
    e'.right_inv hw1]
end ReciprocityTheory.L2DbarEstimates.F
