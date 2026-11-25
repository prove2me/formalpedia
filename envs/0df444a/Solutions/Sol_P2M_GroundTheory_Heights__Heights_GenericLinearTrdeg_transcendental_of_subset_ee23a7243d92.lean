-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_transcendental_of_subset_ee23a7243d92
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:19.191935+00:00
-- url     : https://prove2.me/submissions/af0d6f0d-111d-4e53-8f02-a4926e7e5972

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PGenericLinearTrdeg

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
open MvPolynomial
open GroundTheory.Heights₂.Heights.GenericLinearTrdeg
namespace GroundTheory.Heights₂.Heights.GenericLinearTrdeg
theorem _root_.solution {A R₁ R₂ : Type*} [CommRing A] [CommRing R₁] [CommRing R₂]
    [Algebra R₁ A] [Algebra R₂ A] (S₁ : Subalgebra R₁ A) (S₂ : Subalgebra R₂ A)
    (h : (S₁ : Set A) ⊆ S₂) {x : A} (hx : Transcendental S₂ x) : Transcendental S₁ x := by
  let f : S₁ →+* S₂ :=
    { toFun := fun y => ⟨y, h y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let _ : Algebra S₁ S₂ := f.toAlgebra
  have : IsScalarTower S₁ S₂ A := .of_algebraMap_eq fun _ => rfl
  refine hx.restrictScalars ?_
  intro a b hab
  apply Subtype.ext
  have hab' := congrArg Subtype.val hab
  exact hab'
end GroundTheory.Heights₂.Heights.GenericLinearTrdeg
