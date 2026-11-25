-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_exists_mul_eq_zero_of_pushout_inl_428d3945dc6e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:05:17.816348+00:00
-- url     : https://prove2.me/submissions/ad442bd0-a72f-4bf8-a120-fc92f7e57f0b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsLocSectionsInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PLocSectionsInj

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
theorem _root_.solution {R A T : CommRingCat.{0}} (f : R ⟶ A) (g : R ⟶ T)
    (M : Submonoid R) (hT : @IsLocalization R _ M T _ g.hom.toAlgebra) (a : A)
    (ha : pushout.inl f g a = 0) : ∃ m ∈ M, f m * a = 0 := by
  algebraize [f.hom, g.hom]
  have e : _ = pushout.inl f g := (CommRingCat.isPushout_tensorProduct R T A).flip.inl_isoPushout_hom
  rw [← e, CommRingCat.comp_apply, ← map_zero
    (CommRingCat.isPushout_tensorProduct R T A).flip.isoPushout.hom.hom] at ha
  have ha' := (CommRingCat.isPushout_tensorProduct R T A).flip.isoPushout.commRingCatIsoToRingEquiv.injective ha
  have hL : IsLocalizedModule M (TensorProduct.mk R T A 1) :=
    (isLocalizedModule_iff_isBaseChange M T _).mpr (TensorProduct.isBaseChange R A T)
  obtain ⟨m, hm⟩ := (IsLocalizedModule.eq_zero_iff M (TensorProduct.mk R T A 1)).mp ha'
  exact ⟨m, m.2, hm⟩
end GroundTheory.Heights₂.Heights.Model
