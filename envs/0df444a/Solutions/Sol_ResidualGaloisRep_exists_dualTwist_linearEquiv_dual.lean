-- Prove2me | solution 1 for ResidualGaloisRep.exists_dualTwist_linearEquiv_dual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/5c0a3307-4256-561d-89ee-9808f9e87f50

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_dualTwist_linearEquiv_dual

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem solution
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p] (ρbar : ResidualGaloisRep k) :
    ∃ (ρbar' : ResidualGaloisRep k) (η : ρbar'.V ≃ₗ[k] Module.Dual k ρbar.V),
      ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : ρbar'.V),
        η (ρbar'.ρ g w) =
          (ZMod.castHom (dvd_refl p) k ((cycloChar p g : (ZMod p)ˣ) : ZMod p)) • ((η w) ∘ₗ (ρbar.ρ g⁻¹)) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set Γ := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

  let χ : Γ → k := fun g => ZMod.castHom (dvd_refl p) k ((cycloChar p g : (ZMod p)ˣ) : ZMod p)
  have hχ_one : χ 1 = 1 := by simp [χ]
  have hχ_mul : ∀ g h : Γ, χ (g * h) = χ g * χ h := by
    intro g h; simp [χ, map_mul, Units.val_mul]

  let ρ' : Γ →* Module.End k (Module.Dual k ρbar.V) :=
    { toFun := fun g => χ g • (ρbar.ρ g⁻¹).dualMap
      map_one' := by
        rw [hχ_one, one_smul, inv_one, map_one]
        exact LinearMap.dualMap_id
      map_mul' := fun g h => by
        show χ (g * h) • (ρbar.ρ (g * h)⁻¹).dualMap =
          (χ g • (ρbar.ρ g⁻¹).dualMap) * (χ h • (ρbar.ρ h⁻¹).dualMap)
        rw [hχ_mul, mul_inv_rev, map_mul, smul_mul_smul_comm]
        rfl }
  have hρ' : ∀ (g : Γ) (w : Module.Dual k ρbar.V), ρ' g w = χ g • (w ∘ₗ ρbar.ρ g⁻¹) := by
    intro g w
    show (χ g • (ρbar.ρ g⁻¹).dualMap) w = _
    rfl

  have hlevel : GaloisFactorsThroughFiniteLevel ρ' := by
    obtain ⟨L, hL, hLρ⟩ := ρbar.factorsThroughFiniteLevel
    haveI := hL
    let S : Set (AlgebraicClosure ℚ) :=
      Set.range (fun t : rootsOfUnity p (AlgebraicClosure ℚ) => ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    haveI : Finite S := (Set.finite_range _).to_subtype
    haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
      IntermediateField.finiteDimensional_adjoin
        (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral)
    refine ⟨L ⊔ IntermediateField.adjoin ℚ S, inferInstance, fun σ hσ => ?_⟩
    have h1 : ρbar.ρ σ = 1 := hLρ σ (fun x hx => hσ x ((le_sup_left : L ≤ L ⊔ IntermediateField.adjoin ℚ S) hx))
    haveI : Fact (1 < p) := ⟨hp.one_lt⟩
    have h2 : cycloChar p σ = 1 := by
      apply Units.ext
      rw [Units.val_one]
      refine (modularCyclotomicCharacter.unique (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
        (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (c := 1) (fun t ht => ?_)).symm
      rw [ZMod.val_one, pow_one]
      have ht' : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ IntermediateField.adjoin ℚ S :=
        IntermediateField.subset_adjoin ℚ S ⟨⟨t, ht⟩, rfl⟩
      exact hσ _ ((le_sup_right : IntermediateField.adjoin ℚ S ≤ L ⊔ IntermediateField.adjoin ℚ S) ht')
    apply LinearMap.ext; intro w
    rw [hρ', Module.End.one_apply]
    have : χ σ = 1 := by simp [χ, h2]
    rw [this, one_smul]
    have hinv : ρbar.ρ σ⁻¹ = 1 := by
      have h := map_mul ρbar.ρ σ⁻¹ σ
      rw [inv_mul_cancel, map_one, h1, mul_one] at h
      exact h.symm
    rw [hinv, Module.End.one_eq_id, LinearMap.comp_id]
  haveI : FiniteDimensional k ρbar.V := Module.finite_of_finrank_eq_succ ρbar.finrank_eq
  let ρbar' : ResidualGaloisRep k :=
    { V := Module.Dual k ρbar.V
      finrank_eq := (Subspace.dual_finrank_eq).trans ρbar.finrank_eq
      ρ := ρ'
      factorsThroughFiniteLevel := hlevel }
  refine ⟨ρbar', LinearEquiv.refl k _, fun g w => ?_⟩
  exact hρ' g w

end S_ResidualGaloisRep_exists_dualTwist_linearEquiv_dual
end P2MW
export P2MW.S_ResidualGaloisRep_exists_dualTwist_linearEquiv_dual (solution)
