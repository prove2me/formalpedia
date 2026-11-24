-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_mul_form_f630f1747419
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:44.309814+00:00
-- url     : https://prove2.me/submissions/00a29c5c-20b8-43f9-a4f3-092bfb044ff6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative

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
universe u
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
open Classical
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {x y : MRing ι R} {j : K → ℕ}
    (hy : IsMultiHomog y j) (n : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) n (x * y) =
      if j ≤ n then weightedHomogeneousComponent (blockWeight ι) (n - j) x * y else 0 := by
  let _ := MvPolynomial.weightedGradedAlgebra R (blockWeight ι)
  rw [← weightedDecomposition.decompose'_apply, ← weightedDecomposition.decompose'_apply]
  exact DirectSum.coe_decompose_mul_of_right_mem
    (𝒜 := weightedHomogeneousSubmodule R (blockWeight ι)) n hy
end GroundTheory.Heights₂.Heights.NumbersDVR
