-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_CutPieces_component_mul_68293a88f0c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:06:09.150529+00:00
-- url     : https://prove2.me/submissions/7d2b4164-317d-432a-aa4c-33649b3bc30c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutPieces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.CutPieces
variable {F : Type*} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open Classical
namespace GroundTheory.Heights₂.Heights.NumbersDVR.CutPieces
theorem _root_.solution {x : MRing ι F} {e : K → ℕ} (hx : IsMultiHomog x e) (y : MRing ι F)
    (m : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) m (x * y) =
      if e ≤ m then x * weightedHomogeneousComponent (blockWeight ι) (m - e) y else 0 := by
  have key : ∀ (p : MRing ι F) (n : K → ℕ),
      (DirectSum.decompose (weightedHomogeneousSubmodule F (blockWeight ι)) p n : MRing ι F) =
        weightedHomogeneousComponent (blockWeight ι) n p :=
    fun p n => weightedDecomposition.decompose'_apply F _ p n
  have hx' : x ∈ weightedHomogeneousSubmodule F (blockWeight ι) e := hx
  split_ifs with h
  · have := DirectSum.coe_decompose_mul_of_left_mem_of_le
      (𝒜 := weightedHomogeneousSubmodule F (blockWeight ι)) (b := y) hx' h
    rwa [key, key] at this
  · have := DirectSum.coe_decompose_mul_of_left_mem_of_not_le
      (𝒜 := weightedHomogeneousSubmodule F (blockWeight ι)) (b := y) (n := m) hx' h
    rwa [key] at this
end GroundTheory.Heights₂.Heights.NumbersDVR.CutPieces
