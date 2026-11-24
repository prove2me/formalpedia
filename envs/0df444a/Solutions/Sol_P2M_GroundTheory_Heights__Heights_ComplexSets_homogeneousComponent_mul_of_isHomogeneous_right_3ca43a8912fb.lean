-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_homogeneousComponent_mul_of_isHomogeneous_right_3ca43a8912fb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:13.829716+00:00
-- url     : https://prove2.me/submissions/0d83404f-bff7-4d8b-9f7f-0ba0885b0a8e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution {σ : Type*} (a g : MvPolynomial σ ℂ)
    {e : ℕ} (hg : g.IsHomogeneous e) (k : ℕ) :
    homogeneousComponent k (a * g) = if e ≤ k then homogeneousComponent (k - e) a * g else 0 := by
  have hd : ∀ (p : MvPolynomial σ ℂ) (i : ℕ),
      (DirectSum.decompose (homogeneousSubmodule σ ℂ) p i : MvPolynomial σ ℂ) =
        homogeneousComponent i p := fun p i => decomposition.decompose'_apply p i
  have h := DirectSum.coe_decompose_mul_of_right_mem (homogeneousSubmodule σ ℂ) k (a := a)
    ((mem_homogeneousSubmodule e g).2 hg)
  simpa only [hd] using h
end GroundTheory.Heights₂.Heights.ComplexSets
