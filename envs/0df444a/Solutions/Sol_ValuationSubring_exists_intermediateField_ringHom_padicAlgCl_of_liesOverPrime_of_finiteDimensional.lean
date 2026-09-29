-- Prove2me | solution 1 for ValuationSubring.exists_intermediateField_ringHom_padicAlgCl_of_liesOverPrime_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/0166eb7f-1726-521b-ad6e-64a80bca109e

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime
import Theorems.Thm_padicPlace_liesOverPrime
import Theorems.Thm_ValuationSubring_localGaloisToGlobal_mem_inertiaSubgroupIn_padicPlace
import Theorems.Thm_ValuationSubring_mem_inertiaSubgroupIn_pointwise_smul_iff
import Theorems.Thm_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_intermediateField_ringHom_padicAlgCl_of_liesOverPrime_of_finiteDimensional

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open scoped Pointwise

local instance isAlgebraicQbar_c7 : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance instTowerQqPadic_c7 (p : ℕ) [Fact p.Prime] : IsScalarTower ℚ ℚ_[p] (PadicAlgCl p) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F]
    (hOF : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ F) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K)
      (ι : AlgebraicClosure ℚ →+* PadicAlgCl p) (φ : O →+* PadicAlgCl.ringOfIntegers p K),
      (∀ x : O, ((φ x : PadicAlgCl.ringOfIntegers p K) : PadicAlgCl p) = ι (algebraMap O (AlgebraicClosure ℚ) x)) ∧
      (∀ t : AlgebraicClosure ℚ, P.valuation t < 1 ↔ ‖ι t‖ < 1) ∧
      (∀ t : AlgebraicClosure ℚ, t ∈ P ↔ ‖ι t‖ ≤ 1) ∧
      (∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (τl : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ s : PadicAlgCl p, τl s = σ s) → σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∃ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ),
          (∀ t : AlgebraicClosure ℚ, τ' t = τ t) ∧ τ ∈ P.inertiaSubgroupIn ℚ ∧ ∀ t : AlgebraicClosure ℚ, ι (τ' t) = τl (ι t)) := by
  classical

  obtain ⟨g, hg⟩ := ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime (Fact.out : p.Prime)
    (padicPlace p) P (padicPlace_liesOverPrime p) hP

  let ι' : AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl p :=
    (padicEmbedding p).comp (g.symm : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ)
  let ι : AlgebraicClosure ℚ →+* PadicAlgCl p := ι'.toRingHom
  have hι : ∀ t, ι t = padicEmbedding p (g.symm t) := fun t => rfl
  have hι'ι : ∀ t, ι' t = ι t := fun t => rfl
  have hginv : ∀ t, g⁻¹ t = g.symm t := fun t => rfl
  have hmem : ∀ t : AlgebraicClosure ℚ, t ∈ P ↔ ‖ι t‖ ≤ 1 := by
    intro t
    rw [← hg, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, mem_padicPlace_iff,
      hginv, hι, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  have hval : ∀ t : AlgebraicClosure ℚ, P.valuation t < 1 ↔ ‖ι t‖ < 1 := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp
    have hvpos : 0 < P.valuation t := (Valuation.pos_iff _).2 ht
    have hnpos : 0 < ‖ι t‖ := norm_pos_iff.2 ((map_ne_zero ι).2 ht)
    have h1 : P.valuation t < 1 ↔ ¬ t⁻¹ ∈ P := by
      rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, inv_le_one₀ hvpos, not_le]
    have h2 : ‖ι t‖ < 1 ↔ ¬ t⁻¹ ∈ P := by
      rw [hmem, map_inv₀, norm_inv, inv_le_one₀ hnpos, not_le]
    rw [h1, h2]

  let b := Module.finBasis ℚ F
  let S : Set (PadicAlgCl p) := Set.range fun i => ι' ((b i : F) : AlgebraicClosure ℚ)
  let K : IntermediateField ℚ_[p] (PadicAlgCl p) := IntermediateField.adjoin ℚ_[p] S
  have hSint : ∀ x ∈ S, IsIntegral ℚ_[p] x := by
    rintro _ ⟨i, rfl⟩
    exact IsIntegral.tower_top (R := ℚ)
      ((Algebra.IsIntegral.isIntegral (R := ℚ) ((b i : F) : AlgebraicClosure ℚ)).map ι')
  haveI : Finite S := Set.finite_range _ |>.to_subtype
  have hKfd : FiniteDimensional ℚ_[p] K := IntermediateField.finiteDimensional_adjoin hSint
  have hιF : ∀ x : F, ι ((x : F) : AlgebraicClosure ℚ) ∈ K := by
    intro x
    have hx : (x : F) ∈ Submodule.span ℚ (Set.range b) := by rw [b.span_eq]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact IntermediateField.subset_adjoin ℚ_[p] S ⟨i, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [IntermediateField.coe_add, map_add]
      exact add_mem hy hz
    | smul c y _ hy =>
      rw [IntermediateField.coe_smul, Algebra.smul_def, map_mul]
      refine mul_mem ?_ hy
      rw [eq_ratCast, map_ratCast, ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)) c]
      exact K.algebraMap_mem _

  have hιO : ∀ x : O, ι (algebraMap O (AlgebraicClosure ℚ) x) ∈ PadicAlgCl.ringOfIntegers p K := fun x =>
    ⟨(PadicAlgCl.isIntegral_padicInt_iff_norm_le_one p _).2 ((hmem _).1 (hOP x)),
      hιF ⟨_, hOF x⟩⟩
  let φ : O →+* PadicAlgCl.ringOfIntegers p K :=
    { toFun := fun x => ⟨ι (algebraMap O (AlgebraicClosure ℚ) x), hιO x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have hφ : ∀ x : O, ((φ x : PadicAlgCl.ringOfIntegers p K) : PadicAlgCl p) = ι (algebraMap O (AlgebraicClosure ℚ) x) :=
    fun x => rfl
  refine ⟨K, hKfd, ι, φ, hφ, hval, hmem, ?_⟩

  intro σ τl hτσ hσ
  let τ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := localGaloisToGlobal p σ
  have hτ₀ : τ₀ ∈ (padicPlace p).inertiaSubgroupIn ℚ :=
    ValuationSubring.localGaloisToGlobal_mem_inertiaSubgroupIn_padicPlace p σ hσ
  let τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := g * τ₀ * g⁻¹
  have hτP : τ ∈ P.inertiaSubgroupIn ℚ := by
    rw [← hg, ValuationSubring.mem_inertiaSubgroupIn_pointwise_smul_iff]
    have : g⁻¹ * τ * g = τ₀ := by
      simp only [τ]; group
    rw [this]
    exact hτ₀
  have hιτ : ∀ t, ι (τ t) = τl (ι t) := by
    intro t
    rw [hι, hι, hτσ]
    show padicEmbedding p (g.symm ((g * τ₀ * g⁻¹) t)) = σ (padicEmbedding p (g.symm t))
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.symm_apply_apply, hginv,
      padicEmbedding_localGaloisToGlobal]
  have hτO : ∀ x : O, τ (algebraMap O (AlgebraicClosure ℚ) x) = algebraMap O (AlgebraicClosure ℚ) x := by
    intro x
    apply ι.injective
    rw [hιτ, ← hφ]
    exact τl.commutes (φ x)
  let τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ := AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) hτO
  exact ⟨τ, τ', fun t => rfl, hτP, hιτ⟩

end S_ValuationSubring_exists_intermediateField_ringHom_padicAlgCl_of_liesOverPrime_of_finiteDimensional
end P2MW
export P2MW.S_ValuationSubring_exists_intermediateField_ringHom_padicAlgCl_of_liesOverPrime_of_finiteDimensional (solution)
