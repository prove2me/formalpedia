-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_BlockSurjectivity_withBlock_of_ne_12930e8adeee
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:56.651833+00:00
-- url     : https://prove2.me/submissions/8ecfa1d3-bdb2-4f7c-9e70-4b1c14b8a1d3

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
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.BlockSurjectivity
theorem _root_.solution {k₀ k : ι} (h : k ≠ k₀) (w₀ : Fin (n k₀ + 1) → ℂ) (x : Coord n → ℂ) :
    withBlock k₀ w₀ x k = fun i ↦ x ⟨k, i⟩ :=
  Function.update_of_ne h _ _
end GroundTheory.Heights₂.Heights.BlockSurjectivity
