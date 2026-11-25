-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalGraphMass_frameFibreCount_image_repr_0c3b2d2c01ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:02.631547+00:00
-- url     : https://prove2.me/submissions/414bb8c6-1d6f-432c-b7c1-9a8d9c14bd03

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalGraphMass_frameProj_basisFun_repr_3fd2d1412cc3

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
open MeasureTheory Function
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LocalGraphMass
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.LocalGraphMass
theorem _root_.solution (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (A : Set (EuclideanSpace ℂ (Fin n))) (x : I → ℂ) :
    frameFibreCount (EuclideanSpace.basisFun (Fin n) ℂ) I (b.repr '' A) x =
      frameFibreCount b I A x := by
  have h : {y ∈ b.repr '' A | frameProj (EuclideanSpace.basisFun (Fin n) ℂ) I y = x} =
      b.repr '' {z ∈ A | frameProj b I z = x} := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      exact ⟨z, ⟨hz, by rwa [frameProj_basisFun_repr] at hy⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, by rw [frameProj_basisFun_repr]; exact hzx⟩
  simp only [frameFibreCount]
  rw [h, b.repr.injective.injOn.encard_image]
end GroundTheory.Heights₂.Heights.LocalGraphMass
