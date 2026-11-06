-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.kaehler_field_map_zero_heightOne_clear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:12.568193+00:00
-- url     : https://prove2.me/submissions/ef4adb76-ec43-4986-bb33-edb8ae0d04b6

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerImage
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.Algebra.GroupWithZero.Action.Units
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerInjective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehler_field_map_comp


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]
variable [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
variable [SMulCommClass R A K] [IsDedekindDomain A] [IsFractionRing A K]
variable (H : IsDedekindDomain.HeightOneSpectrum A) (T : ValuationSubring K)
variable [Algebra R T] [Algebra T K] [IsScalarTower R T K] [SMulCommClass R T K]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (heq : H.valuationSubringAtPrime K = T)
    (hT : ∀ t : T, algebraMap T K t = t.val)
    (hTin : Function.Injective (KaehlerDifferential.map R R T K))
    (tau : KaehlerDifferential R A)
    (hzero : KaehlerDifferential.map R R A K tau = 0) :
    ∃ s : A, s ∉ H.asIdeal ∧ s • tau = 0 := by
  let S := H.valuationSubringAtPrime K
  let e : S ≃+* T := kaehlerValuationSubringEquiv S T heq
  let : Algebra A T := (e.toRingHom.comp (algebraMap A S)).toAlgebra
  let : IsLocalization H.asIdeal.primeCompl T :=
    (IsLocalization.isLocalization_iff_of_ringEquiv H.asIdeal.primeCompl e).mp inferInstance
  let : IsScalarTower A T K := .of_algebraMap_eq fun a => by
    rw [hT]
    exact IsScalarTower.algebraMap_apply A S K a
  let : IsScalarTower R A T := .of_algebraMap_eq fun r => by
    apply Subtype.val_injective
    change (algebraMap R T r).val = (e (algebraMap A S (algebraMap R A r))).val
    calc
      _ = algebraMap T K (algebraMap R T r) := (hT _).symm
      _ = algebraMap R K r := (IsScalarTower.algebraMap_apply R T K r).symm
      _ = algebraMap A K (algebraMap R A r) := IsScalarTower.algebraMap_apply R A K r
      _ = _ := IsScalarTower.algebraMap_apply A S K _
  let : SMulCommClass R A T :=
    { smul_comm := fun r a t => by simp only [Algebra.smul_def]; ring }
  have ht : KaehlerDifferential.map R R A T tau = 0 := by
    apply hTin
    rw [map_zero, ← kaehler_field_map_comp R A T K]
    exact hzero
  obtain ⟨s,hs⟩ := (IsLocalizedModule.eq_zero_iff H.asIdeal.primeCompl
    (KaehlerDifferential.map R R A T)).mp ht
  change s.val • tau = 0 at hs
  exact ⟨s.val,s.property,hs⟩
end QEC.Coding.AlgebraicGeometry
