-- Prove2me | solution 1 for ResidualGaloisRep.exists_charpoly_eq_mul_of_isTaylorWilesPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/94683f4a-7d6f-51fd-a7bc-d4855c100aa0

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_TaylorWiles_Primes
import Theorems.Thm_NumberField_exists_isFrobenius_lift_arithFrobAt
import Theorems.Thm_NumberField_exists_valuationSubring_eq_localization
import Theorems.Thm_ValuationSubring_isFrobeniusAt_of_forall_smul_sub_pow_mem
import Theorems.Thm_GlobalGaloisRep_IsUnramifiedAt_exists_apply_eq_apply_conj_of_isFrobeniusAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_charpoly_eq_mul_of_isTaylorWilesPrime
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"

set_option autoImplicit false

open Polynomial

namespace SeedF

open NumberField

theorem charpoly_eq_of_hasDistinctRationalEigenvalues {k : Type*} [Field k] (M : Matrix (Fin 2) (Fin 2) k)
    (hM : M.HasDistinctRationalEigenvalues) : ∃ α β : k, α ≠ β ∧ M.charpoly = (X - C α) * (X - C β) := by
  obtain ⟨α, β, hne, htr, hdet⟩ := hM
  refine ⟨α, β, hne, ?_⟩
  rw [Matrix.charpoly_fin_two, htr, hdet, C_add, C_mul]
  ring

theorem charpoly_units_conj {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (u : (V →ₗ[k] V)ˣ) (f : V →ₗ[k] V) :
    LinearMap.charpoly ((u : V →ₗ[k] V) * f * ((u⁻¹ : (V →ₗ[k] V)ˣ) : V →ₗ[k] V)) = LinearMap.charpoly f := by
  classical
  let b := Module.Free.chooseBasis k V
  rw [← LinearMap.charpoly_toMatrix _ b, ← LinearMap.charpoly_toMatrix f b, LinearMap.toMatrix_mul,
    LinearMap.toMatrix_mul, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← LinearMap.toMatrix_mul]
  have : ((u⁻¹ : (V →ₗ[k] V)ˣ) : V →ₗ[k] V) * (u : V →ₗ[k] V) = 1 := u.inv_mul
  rw [this, LinearMap.toMatrix_one, Matrix.one_mul]

theorem exists_ideal_liesOver_ratPrimeIdeal (L₀ : Type*) [Field L₀] [NumberField L₀] {q : ℕ} (hq : q.Prime) :
    ∃ Q : Ideal (𝓞 L₀), Q.IsMaximal ∧ Q.LiesOver (FrobeniusDensity.ratPrimeIdeal q) := by
  haveI : Fact q.Prime := ⟨hq⟩
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral (FrobeniusDensity.ratPrimeIdeal q)

end SeedF

open NumberField in
theorem solution
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L₀] [IsGalois ℚ L₀]
    (b : Module.Basis (Fin 2) k ρbar.V) (ρmat : TaylorWiles.ResidualRep (↥L₀) k)
    (hρmat : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ρmat (AlgEquiv.restrictNormalHom (↥L₀) σ) = LinearMap.toMatrix b b (ρbar.ρ σ))
    (p n q : ℕ) (htw : TaylorWiles.IsTaylorWilesPrime ρmat p n q) (hunr : ρbar.IsUnramifiedAt q) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
        ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β) := by
  intro P hP φ hφ
  obtain ⟨hq, -, hfrob⟩ := htw
  haveI : Fact q.Prime := ⟨hq⟩

  obtain ⟨Q, hQmax, hQover⟩ := SeedF.exists_ideal_liesOver_ratPrimeIdeal (↥L₀) hq
  haveI : Q.IsMaximal := hQmax
  haveI : Q.LiesOver (FrobeniusDensity.ratPrimeIdeal q) := hQover
  haveI : Finite (𝓞 (↥L₀) ⧸ Q) :=
    FrobeniusDensity.finite_quotient_of_ne_bot (FrobeniusDensity.ne_bot_of_liesOver_ratPrimeIdeal hq)
  have hreg := hfrob Q inferInstance inferInstance inferInstance

  obtain ⟨Qt, hQt, τ, hover, hres, hstab, hfr⟩ := NumberField.exists_isFrobenius_lift_arithFrobAt L₀ q hq Q
  haveI : Qt.IsMaximal := hQt
  obtain ⟨A, hA⟩ := NumberField.exists_valuationSubring_eq_localization Qt
  have hqQ : ((q : ℤ) : 𝓞 (↥L₀)) ∈ Q := by
    have h1 : (q : ℤ) ∈ FrobeniusDensity.ratPrimeIdeal q := Ideal.mem_span_singleton_self _
    have h1' := (Ideal.mem_of_liesOver Q (FrobeniusDensity.ratPrimeIdeal q) (q : ℤ)).mp h1
    simpa using h1'
  have hqQt : (q : 𝓞 (AlgebraicClosure ℚ)) ∈ Qt := by
    haveI := hover
    have h2 := (Ideal.mem_of_liesOver Qt Q ((q : ℤ) : 𝓞 (↥L₀))).mp hqQ
    simpa using h2
  obtain ⟨hAq, hτ⟩ :=
    ValuationSubring.isFrobeniusAt_of_forall_smul_sub_pow_mem Qt q hq hqQt τ hstab hfr A hA

  have hunr' : GlobalGaloisRep.IsUnramifiedAt ρbar.ρ.toHomUnits q := by
    intro B hB σ hσ
    rw [MonoidHom.mem_ker]
    ext1
    rw [MonoidHom.coe_toHomUnits, Units.val_one]
    exact hunr B hB σ hσ
  obtain ⟨γ, hγ⟩ :=
    GlobalGaloisRep.IsUnramifiedAt.exists_apply_eq_apply_conj_of_isFrobeniusAt hq hunr' hAq hP hτ hφ
  have hconj : ρbar.ρ φ = ρbar.ρ γ * ρbar.ρ τ * ρbar.ρ γ⁻¹ := by
    have := congrArg Units.val hγ
    simp only [MonoidHom.coe_toHomUnits, map_mul] at this
    exact this
  have hcp : LinearMap.charpoly (ρbar.ρ φ) = LinearMap.charpoly (ρbar.ρ τ) := by
    haveI : Module.Finite k ρbar.V := inferInstance
    rw [hconj]
    have hu : ρbar.ρ γ⁻¹ = ((ρbar.ρ.toHomUnits γ)⁻¹ : (ρbar.V →ₗ[k] ρbar.V)ˣ) := by
      rw [← map_inv, MonoidHom.coe_toHomUnits]
    rw [hu, show ρbar.ρ γ = ((ρbar.ρ.toHomUnits γ : (ρbar.V →ₗ[k] ρbar.V)ˣ) : ρbar.V →ₗ[k] ρbar.V) from rfl]
    exact SeedF.charpoly_units_conj (ρbar.ρ.toHomUnits γ) (ρbar.ρ τ)

  have hmat : LinearMap.toMatrix b b (ρbar.ρ τ) = ρmat (arithFrobAt ℤ (↥L₀ ≃ₐ[ℚ] ↥L₀) Q) := by
    rw [← hρmat τ, ← hres]
    rfl
  obtain ⟨α, β, hne, hM⟩ := SeedF.charpoly_eq_of_hasDistinctRationalEigenvalues _ hreg
  refine ⟨α, β, hne, ?_⟩
  rw [hcp, ← LinearMap.charpoly_toMatrix (ρbar.ρ τ) b, hmat, hM]

#print axioms solution

end S_ResidualGaloisRep_exists_charpoly_eq_mul_of_isTaylorWilesPrime
end P2MW
export P2MW.S_ResidualGaloisRep_exists_charpoly_eq_mul_of_isTaylorWilesPrime (solution)
