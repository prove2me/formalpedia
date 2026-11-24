-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockSurjectivity_weight_coordDeg_apply_695929babdd5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:03:39.636346+00:00
-- url     : https://prove2.me/submissions/c1b1057d-a339-4ac7-a0de-6b1030673585

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock

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
theorem _root_.solution (μ : Coord n →₀ ℕ) (k : ι) :
    Finsupp.weight (coordDeg n) μ k = ∑ i, μ ⟨k, i⟩ := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype μ (fun i c ↦ c • coordDeg n i) (fun _ ↦ zero_smul _ _), Finset.sum_apply,
    Fintype.sum_sigma]
  simp [coordDeg, Pi.single_apply]
end GroundTheory.Heights₂.Heights.BlockSurjectivity
