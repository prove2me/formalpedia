-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_apply_0f53360b901e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:03:39.584887+00:00
-- url     : https://prove2.me/submissions/e01a2a93-c554-4546-bc25-488c7b5d3840

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
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.BlockSurjectivity
theorem _root_.solution (M : Finset (Coord n →₀ ℕ)) (g : MvPolynomial (Coord n) ℂ) (μ : M) :
    coeffVec M g μ = coeff μ.1 g := rfl
end GroundTheory.Heights₂.Heights.BlockSurjectivity
