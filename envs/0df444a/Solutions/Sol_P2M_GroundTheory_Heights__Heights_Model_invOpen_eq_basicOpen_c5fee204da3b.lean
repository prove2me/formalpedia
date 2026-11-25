-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_invOpen_eq_basicOpen_c5fee204da3b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:05:13.019813+00:00
-- url     : https://prove2.me/submissions/7691083a-38da-4257-b0cc-a53808c4edbf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry Opposite
noncomputable section
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {X : Scheme.{0}} (f : X ⟶ SpecZ) (k : ℤ) :
    invOpen f k = X.basicOpen ((k : Γ(X, f ⁻¹ᵁ ⊤))) := by
  have h : invOpen f k = f ⁻¹ᵁ (SpecZ.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv k)) := by
    unfold invOpen
    exact congrArg (f ⁻¹ᵁ ·) (basicOpen_eq_of_affine (R := CommRingCat.of ℤ) k).symm
  rw [h, Scheme.preimage_basicOpen]
  congr 1
  simp only [eq_intCast]
  exact map_intCast (f.app ⊤).hom k
end GroundTheory.Heights₂.Heights.Model
