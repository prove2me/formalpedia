-- Prove2me | solution 1 for ResidualGaloisRep.exists_taylorWilesPrime_notMem_of_isAbsolutelyIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/2d0bde95-4c75-51a0-a413-b9046550ce52

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_TaylorWiles_Primes
import Definitions.Def_TaylorWiles_CyclotomicChar
import Definitions.Def_GaloisRep_GlobalUnramifiedAt
import Theorems.Thm_exists_residualRep_descent
import Theorems.Thm_ResidualGaloisRep_exists_taylorWilesPrime_notMem_of_seed
import Theorems.Thm_TaylorWiles_exists_mem_ker_cycloChar_hasDistinctRationalEigenvalues
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top
import Theorems.Thm_GlobalGaloisRep_exists_finset_forall_isUnramifiedAt_of_isOpen_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_taylorWilesPrime_notMem_of_isAbsolutelyIrreducible
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois"

set_option autoImplicit false

open Polynomial IntermediateField NumberField

noncomputable section

namespace P2mTW1

abbrev Qb := AlgebraicClosure ℚ
abbrev Γ := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

scoped instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.isAlgebraic ℚ
  rfl
  rfl
scoped instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.instIsAlgClosure ℚ
  rfl
  rfl
scoped instance normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ _

theorem isIntegral_algebraicClosure_rat : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := by
  have h := Subsingleton.elim (AlgebraicClosure.instAlgebra ℚ) (DivisionRing.toRatAlgebra)
  have := AlgebraicClosure.isAlgebraic ℚ
  rw [h] at this
  exact Algebra.IsAlgebraic.isIntegral

private lemma _root_.P2mTW1.exists_isPrimitiveRoot (N : ℕ) [NeZero N] : ∃ ζ₀ : Qb, IsPrimitiveRoot ζ₀ N :=
  IsCyclotomicExtension.exists_isPrimitiveRoot (S := ({N} : Set ℕ)) Qb Qb
    (Set.mem_singleton N) (NeZero.ne N)

p2m_export "P2mTW1" "exists_isPrimitiveRoot"

lemma trace_det_of_charpoly_eq {k : Type} [Field k] (M : Matrix (Fin 2) (Fin 2) k) {α β : k}
    (h : M.charpoly = (X - C α) * (X - C β)) :
    M.trace = α + β ∧ M.det = α * β := by
  have hexp : (X - C α) * (X - C β) = X ^ 2 - C (α + β) * X + C (α * β) := by
    simp only [map_add, map_mul]; ring
  have h1 : M.charpoly.coeff 1 = -(α + β) := by
    rw [h, hexp]
    simp [coeff_C]
  have h0 : M.charpoly.coeff 0 = α * β := by
    rw [h, hexp]
    simp [coeff_C]
  refine ⟨?_, ?_⟩
  · rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
    simp [h1]
  · rw [Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, h0]
    ring

theorem main {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (ρbar : ResidualGaloisRep k)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hsplit : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∃ α β : k, LinearMap.charpoly (ρbar.ρ σ) = (X - C α) * (X - C β))
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (n : ℕ) (S : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ S ∧ q ≡ 1 [MOD p ^ n] ∧ ρbar.IsUnramifiedAt q ∧
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
          ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β) := by
  classical

  obtain ⟨L, hLfd, hL⟩ := ρbar.factorsThroughFiniteLevel
  haveI := hLfd
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ₀, hζ₀⟩ := exists_isPrimitiveRoot (p ^ n)
  have hζint : IsIntegral ℚ ζ₀ := (isIntegral_algebraicClosure_rat).isIntegral ζ₀
  haveI : FiniteDimensional ℚ ℚ⟮ζ₀⟯ := adjoin.finiteDimensional hζint
  set L' : IntermediateField ℚ Qb := L ⊔ ℚ⟮ζ₀⟯ with hL'
  haveI : FiniteDimensional ℚ L' := finiteDimensional_sup L ℚ⟮ζ₀⟯
  set L₀ : IntermediateField ℚ Qb := normalClosure ℚ L' Qb with hL₀
  haveI hN : Normal ℚ L₀ := normalClosure.normal ℚ L' Qb
  haveI : FiniteDimensional ℚ L₀ := normalClosure.is_finiteDimensional ℚ L' Qb
  haveI : NumberField L₀ := NumberField.mk
  haveI : IsGalois ℚ L₀ := ⟨⟩
  have hLL₀ : L ≤ L₀ := le_sup_left.trans (le_normalClosure L')
  have hζL₀ : ζ₀ ∈ L₀ :=
    (le_sup_right.trans (le_normalClosure L')) (mem_adjoin_simple_self ℚ ζ₀)
  have hker : ∀ σ : Γ, (∀ x ∈ L₀, σ x = x) → ρbar.ρ σ = 1 :=
    fun σ hσ => hL σ (fun x hx => hσ x (hLL₀ hx))

  let b : Module.Basis (Fin 2) k ρbar.V := Module.finBasisOfFinrankEq k ρbar.V ρbar.finrank_eq
  obtain ⟨ρmat, hρmat⟩ := exists_residualRep_descent ρbar L₀ hker b

  set ζ₁ : L₀ := ⟨ζ₀, hζL₀⟩ with hζ₁
  have hζ₁prim : IsPrimitiveRoot ζ₁ (p ^ n) :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap L₀ Qb)
      (by rw [show algebraMap (↥L₀) Qb ζ₁ = ζ₀ from rfl]; exact hζ₀) (algebraMap L₀ Qb).injective
  have hζ₁int : IsIntegral ℤ ζ₁ := hζ₁prim.isIntegral (NeZero.pos _)
  set ζ : 𝓞 L₀ := ⟨ζ₁, hζ₁int⟩ with hζ
  have hζprim : IsPrimitiveRoot ζ (p ^ n) :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 L₀) L₀)
      (by rw [show algebraMap (𝓞 L₀) L₀ ζ = ζ₁ from rfl]; exact hζ₁prim) RingOfIntegers.coe_injective

  have hspan : Submodule.span k (Set.range ⇑ρbar.ρ) = ⊤ :=
    (ρbar.isAbsolutelyIrreducible_iff_span_eq_top).mp habs
  have hirr : Submodule.span k (Set.range ⇑ρmat) = ⊤ := by
    apply top_unique
    have hsub : (LinearMap.toMatrix b b : Module.End k ρbar.V ≃ₗ[k] Matrix (Fin 2) (Fin 2) k) ''
        Set.range ⇑ρbar.ρ ⊆ Set.range ⇑ρmat := by
      rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
      exact ⟨AlgEquiv.restrictNormalHom L₀ σ, hρmat σ⟩
    calc (⊤ : Submodule k (Matrix (Fin 2) (Fin 2) k))
        = Submodule.map ((LinearMap.toMatrix b b : Module.End k ρbar.V ≃ₗ[k]
            Matrix (Fin 2) (Fin 2) k) : Module.End k ρbar.V →ₗ[k] Matrix (Fin 2) (Fin 2) k) ⊤ := by
          rw [Submodule.map_top, LinearEquiv.range]
      _ = Submodule.span k ((LinearMap.toMatrix b b : Module.End k ρbar.V ≃ₗ[k]
            Matrix (Fin 2) (Fin 2) k) '' Set.range ⇑ρbar.ρ) := by
          rw [← hspan, Submodule.map_span]; rfl
      _ ≤ Submodule.span k (Set.range ⇑ρmat) := Submodule.span_mono hsub
  have hsplit' : ∀ g : L₀ ≃ₐ[ℚ] L₀, ∃ a c : k, (ρmat g).trace = a + c ∧ (ρmat g).det = a * c := by
    intro g
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective Qb g
    obtain ⟨α, β, hαβ⟩ := hsplit σ
    refine ⟨α, β, ?_⟩
    rw [hρmat σ]
    apply trace_det_of_charpoly_eq
    rw [LinearMap.charpoly_toMatrix, hαβ]

  obtain ⟨σ, hσ, hreg⟩ :=
    TaylorWiles.exists_mem_ker_cycloChar_hasDistinctRationalEigenvalues hp2 ρmat n hζprim h2
      hirr hsplit'
  have hpS : p ∈ insert p S := Finset.mem_insert_self p S
  let Λ := TaylorWiles.cyclotomicLevelStructureOfIsPrimitiveRoot (↥L₀) p n hpS hζprim
  have hΛN : Λ.N = (TaylorWiles.cycloChar hζprim).ker := rfl
  let seed : TaylorWiles.Seed ρmat p n (insert p S) :=
    { σ := σ
      regular := hreg
      congruent := fun ℓ hℓ hreal => Λ.congruent σ (hΛN ▸ hσ) ℓ hℓ hreal }

  have hopen : IsOpen ((ρbar.ρ.toHomUnits.ker : Subgroup Γ) : Set Γ) := by
    apply Subgroup.isOpen_mono (H₁ := L.fixingSubgroup) _
      (IntermediateField.fixingSubgroup_isOpen L)
    intro τ hτ
    rw [MonoidHom.mem_ker]
    ext1
    rw [MonoidHom.coe_toHomUnits, Units.val_one]
    exact hL τ ((IntermediateField.mem_fixingSubgroup_iff (K := L) τ).mp hτ)
  obtain ⟨B, hB⟩ :=
    GlobalGaloisRep.exists_finset_forall_isUnramifiedAt_of_isOpen_ker ρbar.ρ.toHomUnits hopen
  have hBunr : ∀ q : ℕ, q.Prime → q ∉ B → ρbar.IsUnramifiedAt q := by
    intro q hq hqB A hA τ hτ
    have h := (hB q hq hqB) A hA hτ
    rw [MonoidHom.mem_ker] at h
    have h' := congrArg Units.val h
    rwa [MonoidHom.coe_toHomUnits, Units.val_one] at h'

  obtain ⟨q, hq, hqS, -, hmod, hunr, hfrob⟩ :=
    ResidualGaloisRep.exists_taylorWilesPrime_notMem_of_seed ρbar L₀ b ρmat hρmat p n seed B hBunr
  exact ⟨q, hq, fun h => hqS (Finset.mem_insert_of_mem h), hmod, hunr, hfrob⟩

end P2mTW1
p2m_reactivate "P2MW.S_ResidualGaloisRep_exists_taylorWilesPrime_notMem_of_isAbsolutelyIrreducible.P2mTW1"

end
p2m_reactivate "P2MW.S_ResidualGaloisRep_exists_taylorWilesPrime_notMem_of_isAbsolutelyIrreducible.P2mTW1"

theorem solution
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (ρbar : ResidualGaloisRep k)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hsplit : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∃ α β : k, LinearMap.charpoly (ρbar.ρ σ) = (X - C α) * (X - C β))
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (n : ℕ) (S : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ S ∧ q ≡ 1 [MOD p ^ n] ∧ ρbar.IsUnramifiedAt q ∧
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
          ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β) :=
  P2mTW1.main h2 ρbar habs hsplit p hp2 n S

end S_ResidualGaloisRep_exists_taylorWilesPrime_notMem_of_isAbsolutelyIrreducible
end P2MW
export P2MW.S_ResidualGaloisRep_exists_taylorWilesPrime_notMem_of_isAbsolutelyIrreducible (solution)
