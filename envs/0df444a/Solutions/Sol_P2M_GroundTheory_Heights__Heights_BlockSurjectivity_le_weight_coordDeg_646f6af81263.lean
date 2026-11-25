-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockSurjectivity_le_weight_coordDeg_646f6af81263
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:33.906622+00:00
-- url     : https://prove2.me/submissions/7f1fd7ca-6f7c-48bd-bead-54d772b1a2a2

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
theorem _root_.solution (μ : Coord n →₀ ℕ) (v : Coord n) :
    μ v ≤ Finsupp.weight (coordDeg n) μ v.1 := by
  rw [weight_coordDeg_apply]
  exact Finset.single_le_sum (f := fun i ↦ μ ⟨v.1, i⟩) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ v.2)
end GroundTheory.Heights₂.Heights.BlockSurjectivity
