-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockSurjectivity_withBlock_of_ne_12930e8adeee
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:52:11.157054+00:00
-- url     : https://prove2.me/submissions/008fc561-d2d4-4da5-ae5b-4f87afe52bb2

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


theorem solution {k₀ k : ι} (h : k ≠ k₀) (w₀ : Fin (n k₀ + 1) → ℂ) (x : Coord n → ℂ) :
    withBlock k₀ w₀ x k = fun i ↦ x ⟨k, i⟩ := by
  simp_all [withBlock]
