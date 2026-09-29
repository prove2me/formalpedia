-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.forall_algebraMap_eq_cyclicQuotientJ_of_exists_of_raw_rigidDataPow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/1fd9f17d-cfb9-564d-b03d-155f0ce171d5

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Definitions.Def_WeierstrassCurve_MapPoint
import Definitions.Def_ModularCurve_ModuliPoint
import Theorems.Thm_exists_isAlgClosed_algHom_algHom_of_injective
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_addOrderOf_eq_forall_isRoot_level_fst_of_raw_rigidDataPow
import Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_map_eq_apply_cyclicQuotientJ_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_moduliPoint_mk_eq_of_quot_mk_eq_of_raw_rigidDataPow
import Theorems.Thm_ModularCurve_Gamma0Pair_cyclicQuotientJ_zmultiples_smul_gen_eq_of_mk_eq_mk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_forall_algebraMap_eq_cyclicQuotientJ_of_exists_of_raw_rigidDataPow
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped Classical

namespace F2cAux

theorem cutout_mapPoint {F F' : Type} [Field F] [Field F'] [DecidableEq F] [DecidableEq F'] (σ : F →+* F') {ι : Type}
    {V : WeierstrassCurve F} (tuple : ι → Polynomial F) (pe : ι → ℕ) (g : V.toAffine.Point)
    (hg : ∀ (i : ι) (n : ℕ) (x₁ y₁ : F) (h₁ : V.toAffine.Nonsingular x₁ y₁),
      n • g = .some x₁ y₁ h₁ → addOrderOf (n • g) = pe i → (tuple i).IsRoot x₁) :
    ∀ (i : ι) (n : ℕ) (x₁ y₁ : F') (h₁ : (V.map σ).toAffine.Nonsingular x₁ y₁),
      n • WeierstrassCurve.mapPoint σ g = .some x₁ y₁ h₁ → addOrderOf (n • WeierstrassCurve.mapPoint σ g) = pe i →
      ((tuple i).map σ).IsRoot x₁ := by
  intro i n x₁ y₁ h₁ hn hord
  rw [← WeierstrassCurve.mapPoint_nsmul, WeierstrassCurve.addOrderOf_mapPoint] at hord
  rw [← WeierstrassCurve.mapPoint_nsmul] at hn
  rcases hng : n • g with _ | ⟨x, y, hxy⟩
  · rw [hng] at hn
    change WeierstrassCurve.mapPoint σ 0 = _ at hn
    rw [WeierstrassCurve.mapPoint_zero] at hn
    exact absurd hn.symm (WeierstrassCurve.Affine.Point.some_ne_zero _)
  · rw [hng, WeierstrassCurve.mapPoint_some, WeierstrassCurve.Affine.Point.some.injEq] at hn
    rw [← hn.1]
    exact (hg i n x y hxy hng hord).map

end F2cAux

theorem solution
    (A : Type) [CommRing A] (ℓ' M' q : ℕ) [NeZero M']
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ' D →
        ModularCurve.IsLevelPStructure (C • W) ℓ' (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q)
    (K : Type) [Field K] [Algebra A K] (hM'K : ((M' : ℕ) : K) ≠ 0)
    (x₀ : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).Pt K) (y : K) (d : ℕ) [NeZero d] (hd : d ∣ M')

    (Ω₀ : Type) [Field Ω₀] [IsAlgClosed Ω₀] [DecidableEq Ω₀] [Algebra A Ω₀] [Algebra K Ω₀] [IsScalarTower A K Ω₀]
    (x : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).Raw Ω₀)
    (hx : (Quot.mk _ x : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).Pt Ω₀) =
      (WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map (IsScalarTower.toAlgHom A K Ω₀) x₀)
    (hread : ∀ (g : (x.curve).toAffine.Point),
      (addOrderOf g = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : Ω₀) (h₁ : (x.curve).toAffine.Nonsingular x₁ y₁),
          n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (x.level.1 p).IsRoot x₁) →
      algebraMap K Ω₀ y = WeierstrassCurve.cyclicQuotientJ (x.curve) (AddSubgroup.zmultiples ((M' / d) • g)) d)

    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A Ω] [Algebra K Ω] [IsScalarTower A K Ω]
    (x' : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).Raw Ω)
    (hx' : (Quot.mk _ x' : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).Pt Ω) =
      (WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map (IsScalarTower.toAlgHom A K Ω) x₀)
    (g' : (x'.curve).toAffine.Point)
    (hg' : (addOrderOf g' = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : Ω) (h₁ : (x'.curve).toAffine.Nonsingular x₁ y₁),
          n • g' = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g') = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (x'.level.1 p).IsRoot x₁)) :
    algebraMap K Ω y = WeierstrassCurve.cyclicQuotientJ (x'.curve) (AddSubgroup.zmultiples ((M' / d) • g')) d := by
  classical

  have hM'0 : M' ≠ 0 := NeZero.ne M'

  obtain ⟨Ω', instF, instAC, instAlg, ⟨i₀⟩, ⟨i⟩⟩ :=
    exists_isAlgClosed_algHom_algHom_of_injective K Ω₀ Ω (algebraMap K Ω₀).injective (algebraMap K Ω).injective
  letI : Field Ω' := instF
  letI : IsAlgClosed Ω' := instAC
  letI : Algebra K Ω' := instAlg
  letI algAΩ' : Algebra A Ω' := ((algebraMap K Ω').comp (algebraMap A K)).toAlgebra
  haveI : IsScalarTower A K Ω' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let j₀ : Ω₀ →ₐ[A] Ω' := i₀.restrictScalars A
  let j : Ω →ₐ[A] Ω' := i.restrictScalars A
  have hM'Ω₀ : ((M' : ℕ) : Ω₀) ≠ 0 := by
    intro h; apply hM'K
    exact (algebraMap K Ω₀).injective (by rw [map_natCast, h, map_zero])
  have hM'Ω' : ((M' : ℕ) : Ω') ≠ 0 := by
    intro h; apply hM'K
    exact (algebraMap K Ω').injective (by rw [map_natCast, h, map_zero])

  obtain ⟨g, hg⟩ := WeierstrassCurve.DrinfeldGlobal.exists_addOrderOf_eq_forall_isRoot_level_fst_of_raw_rigidDataPow
    A ℓ' M' q hℓ hM 𝒢 𝒯 Ω₀ hM'Ω₀ x
  have hread₀ := hread g hg

  have hcomp₀ : (j₀.comp (IsScalarTower.toAlgHom A K Ω₀)) = IsScalarTower.toAlgHom A K Ω' := by
    apply AlgHom.ext; intro k
    show i₀ (algebraMap K Ω₀ k) = algebraMap K Ω' k
    exact i₀.commutes k
  have hcomp : (j.comp (IsScalarTower.toAlgHom A K Ω)) = IsScalarTower.toAlgHom A K Ω' := by
    apply AlgHom.ext; intro k
    show i (algebraMap K Ω k) = algebraMap K Ω' k
    exact i.commutes k
  have hcl₀ : (Quot.mk _ ((WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).mapRing j₀ x) :
        (WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).Pt Ω') =
      (WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map (IsScalarTower.toAlgHom A K Ω') x₀ := by
    rw [← ModularCurve.RigidWeierstrassData.map_mk, ← hcomp₀,
      (WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map_comp]
    exact congrArg _ hx
  have hcl : (Quot.mk _ ((WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).mapRing j x') :
        (WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).Pt Ω') =
      (WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map (IsScalarTower.toAlgHom A K Ω') x₀ := by
    rw [← ModularCurve.RigidWeierstrassData.map_mk, ← hcomp,
      (WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map_comp]
    exact congrArg _ hx'

  have hg₀' : addOrderOf (WeierstrassCurve.mapPoint j₀.toRingHom g) = M' ∧
      ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : Ω')
        (h₁ : (((WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).mapRing j₀ x).curve).toAffine.Nonsingular x₁ y₁),
        n • WeierstrassCurve.mapPoint j₀.toRingHom g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ →
        addOrderOf (n • WeierstrassCurve.mapPoint j₀.toRingHom g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
        (((WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).mapRing j₀ x).level.1 p).IsRoot x₁ :=
    ⟨(WeierstrassCurve.addOrderOf_mapPoint _ _).trans hg.1,
     F2cAux.cutout_mapPoint j₀.toRingHom (fun p => x.level.1 p) (fun p : ↥M'.primeFactors => (p : ℕ) ^ M'.factorization (p : ℕ)) g hg.2⟩
  have hg' : addOrderOf (WeierstrassCurve.mapPoint j.toRingHom g') = M' ∧
      ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : Ω')
        (h₁ : (((WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).mapRing j x').curve).toAffine.Nonsingular x₁ y₁),
        n • WeierstrassCurve.mapPoint j.toRingHom g' = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ →
        addOrderOf (n • WeierstrassCurve.mapPoint j.toRingHom g') = (p : ℕ) ^ M'.factorization (p : ℕ) →
        (((WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).mapRing j x').level.1 p).IsRoot x₁ :=
    ⟨(WeierstrassCurve.addOrderOf_mapPoint _ _).trans hg'.1,
     F2cAux.cutout_mapPoint j.toRingHom (fun p => x'.level.1 p) (fun p : ↥M'.primeFactors => (p : ℕ) ^ M'.factorization (p : ℕ)) g' hg'.2⟩

  have hmk := WeierstrassCurve.DrinfeldGlobal.moduliPoint_mk_eq_of_quot_mk_eq_of_raw_rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯 Ω' hM'Ω'
    _ _ (hcl₀.trans hcl.symm) _ _ hg₀' hg'
  have hJ := ModularCurve.Gamma0Pair.cyclicQuotientJ_zmultiples_smul_gen_eq_of_mk_eq_mk hM'Ω' _ _ hmk d hd

  have hbc₀ := WeierstrassCurve.cyclicQuotientJ_map_eq_apply_cyclicQuotientJ_of_isAlgClosed j₀.toRingHom (x.curve)
    (AddSubgroup.zmultiples ((M' / d) • g)) d
  have hbc := WeierstrassCurve.cyclicQuotientJ_map_eq_apply_cyclicQuotientJ_of_isAlgClosed j.toRingHom (x'.curve)
    (AddSubgroup.zmultiples ((M' / d) • g')) d
  rw [AddMonoidHom.map_zmultiples, map_nsmul] at hbc₀ hbc

  apply i.toRingHom.injective
  change j.toRingHom (algebraMap K Ω y) = j.toRingHom _
  rw [← hbc]
  have e1 : j.toRingHom (algebraMap K Ω y) = algebraMap K Ω' y := i.commutes y
  have e2 : j₀.toRingHom (algebraMap K Ω₀ y) = algebraMap K Ω' y := i₀.commutes y
  rw [e1, ← e2, hread₀, ← hbc₀]
  exact hJ

end S_WeierstrassCurve_DrinfeldGlobal_forall_algebraMap_eq_cyclicQuotientJ_of_exists_of_raw_rigidDataPow
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_forall_algebraMap_eq_cyclicQuotientJ_of_exists_of_raw_rigidDataPow (solution)
