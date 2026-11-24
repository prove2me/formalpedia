-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockSurjectivity_mem_offMonos_089e7d3164ba
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:47.986382+00:00
-- url     : https://prove2.me/submissions/b9792968-ad93-4ffc-aa46-97346565f0c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_weight_coordDeg_apply_695929babdd5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Module
noncomputable section
open GroundTheory.Heights₂.Heights.BlockSurjectivity
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.BlockSurjectivity
theorem _root_.solution {k₀ : ι} {D : ℕ} {μ : Coord n →₀ ℕ} :
    μ ∈ offMonos n k₀ D ↔ Finsupp.weight (coordDeg n) μ = offDeg k₀ D := by
  simp only [offMonos, Finset.mem_filter, Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  rw [← h]
  simp only [weight_coordDeg_apply]
  rw [Fintype.sum_sigma]
end GroundTheory.Heights₂.Heights.BlockSurjectivity
