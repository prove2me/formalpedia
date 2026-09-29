-- Prove2me | solution 1 for TateModule.exists_rationalTateModule_linearEquiv_comp_rationalGaloisRep_eq_of_injective_of_card_torsionBy_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8e658f44-fca2-58d1-a13c-491d5fb80dc0

import Mathlib
import Definitions.Def_ModularCurve_JZeroTateModule
import Theorems.Thm_TateModule_exists_linearMap_apply_eq_of_addMonoidHom
import Theorems.Thm_TateModule_nonempty_basis_of_card_torsionBy
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateModule_exists_rationalTateModule_linearEquiv_comp_rationalGaloisRep_eq_of_injective_of_card_torsionBy_eq

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    {J J' : Type} [AddCommGroup J] [AddCommGroup J'] {G : Type} [Monoid G] [DistribMulAction G J] [DistribMulAction G J']
    (β : J →+ J') (hβ : Function.Injective β) (hβG : ∀ (g : G) (x : J), β (g • x) = g • β x)
    (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ)
    (hJ : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ J ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ r)
    (hJ' : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ J' ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ r) :
    ∃ (T : TateModule ℓ J →ₗ[ℤ_[ℓ]] TateModule ℓ J')
      (e : ModularCurve.RationalTateModule ℓ J ≃ₗ[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ J'),
      (∀ (x : TateModule ℓ J) (n : ℕ), ((T x : TateModule ℓ J') : ℕ → J') n = β ((x : ℕ → J) n)) ∧
      (∀ v, e v = T.baseChange ℚ_[ℓ] v) ∧
      ∀ g : G, (e : ModularCurve.RationalTateModule ℓ J →ₗ[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ J') ∘ₗ
          ModularCurve.rationalGaloisRep ℓ J G g =
        ModularCurve.rationalGaloisRep ℓ J' G g ∘ₗ
          (e : ModularCurve.RationalTateModule ℓ J →ₗ[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ J') := by
  classical
  obtain ⟨T, hT, hTinj⟩ := TateModule.exists_linearMap_apply_eq_of_addMonoidHom ℓ β
  have hTi : Function.Injective T := hTinj hβ

  obtain ⟨b⟩ := TateModule.nonempty_basis_of_card_torsionBy ℓ r hJ
  obtain ⟨b'⟩ := TateModule.nonempty_basis_of_card_torsionBy ℓ r hJ'
  let c := Algebra.TensorProduct.basis ℚ_[ℓ] b
  let c' := Algebra.TensorProduct.basis ℚ_[ℓ] b'
  haveI : FiniteDimensional ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ J) := Module.Finite.of_basis c
  haveI : FiniteDimensional ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ J') := Module.Finite.of_basis c'
  have hfr : Module.finrank ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ J) =
      Module.finrank ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ J') := by
    rw [Module.finrank_eq_card_basis c, Module.finrank_eq_card_basis c']

  haveI : Module.Flat ℤ_[ℓ] ℚ_[ℓ] := IsLocalization.flat ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ])
  have hinj : Function.Injective (T.baseChange ℚ_[ℓ]) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap T hTi
  have hbij : Function.Bijective (T.baseChange ℚ_[ℓ]) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hinj⟩
  let e : ModularCurve.RationalTateModule ℓ J ≃ₗ[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ J' :=
    LinearEquiv.ofBijective (T.baseChange ℚ_[ℓ]) hbij
  refine ⟨T, e, hT, fun v => rfl, fun g => ?_⟩

  have hTg : T ∘ₗ TateModule.rep ℓ J G g = TateModule.rep ℓ J' G g ∘ₗ T := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hT, TateModule.rep_apply, TateModule.rep_apply, hT, hβG]
  have : (e : ModularCurve.RationalTateModule ℓ J →ₗ[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ J') = T.baseChange ℚ_[ℓ] := rfl
  rw [this, ModularCurve.rationalGaloisRep_apply, ModularCurve.rationalGaloisRep_apply, ← LinearMap.baseChange_comp,
    ← LinearMap.baseChange_comp, hTg]

end S_TateModule_exists_rationalTateModule_linearEquiv_comp_rationalGaloisRep_eq_of_injective_of_card_torsionBy_eq
end P2MW
export P2MW.S_TateModule_exists_rationalTateModule_linearEquiv_comp_rationalGaloisRep_eq_of_injective_of_card_torsionBy_eq (solution)
