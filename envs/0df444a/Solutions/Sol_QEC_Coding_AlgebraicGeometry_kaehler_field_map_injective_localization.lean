-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.kaehler_field_map_injective_localization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:13.755976+00:00
-- url     : https://prove2.me/submissions/8403f664-cad8-45a8-9fc4-fc7aad2faec2

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerImage
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.Algebra.GroupWithZero.Action.Units
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerInjective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehler_field_map_comp


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (R A B K : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing K]
variable [Algebra R A] [Algebra R B] [Algebra R K]
variable [Algebra A B] [Algebra B K] [Algebra A K]
variable [IsScalarTower R A B] [IsScalarTower R B K] [IsScalarTower R A K]
variable [IsScalarTower A B K]
variable [SMulCommClass R A B] [SMulCommClass R A K] [SMulCommClass R B K]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (S : Submonoid A) [IsLocalization S B]
    (hA : Function.Injective (KaehlerDifferential.map R R A K)) :
    Function.Injective (KaehlerDifferential.map R R B K) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro eta heta
  obtain ⟨⟨tau,s⟩,he⟩ := IsLocalizedModule.surj S (KaehlerDifferential.map R R A B) eta
  change s.val • eta = KaehlerDifferential.map R R A B tau at he
  have htau : KaehlerDifferential.map R R A K tau = 0 := by
    calc
      _ = KaehlerDifferential.map R R B K (KaehlerDifferential.map R R A B tau) :=
        kaehler_field_map_comp R A B K tau
      _ = KaehlerDifferential.map R R B K (s.val • eta) := congrArg _ he.symm
      _ = s.val • KaehlerDifferential.map R R B K eta :=
        ((KaehlerDifferential.map R R B K).restrictScalars A).map_smul s.val eta
      _ = 0 := by rw [heta,smul_zero]
  have htau0 : tau = 0 := hA (htau.trans (map_zero _).symm)
  rw [htau0,map_zero] at he
  have hu := IsLocalization.map_units B s
  exact hu.smul_eq_zero.mp (by rw [IsScalarTower.algebraMap_smul B]; exact he)
end QEC.Coding.AlgebraicGeometry
