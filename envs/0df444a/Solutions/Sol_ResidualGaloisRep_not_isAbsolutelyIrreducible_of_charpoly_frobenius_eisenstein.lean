-- Prove2me | solution 1 for ResidualGaloisRep.not_isAbsolutelyIrreducible_of_charpoly_frobenius_eisenstein
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/afc39392-16cb-5b4a-9e0e-1019406b1244

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv
import Theorems.Thm_ResidualGaloisRep_trace_eq_of_trace_frobenius_eq
import Theorems.Thm_ResidualGaloisRep_charpoly_eq_of_charpoly_frobenius_eq
import Theorems.Thm_FrobeniusDensity_statement
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq
import Theorems.Thm_ResidualGaloisRep_IsAbsolutelyIrreducible_baseChangeAlong
import Theorems.Thm_ResidualGaloisRep_charpoly_baseChangeAlong
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top
import Theorems.Thm_MonoidHom_isOpen_ker_of_cycloCharSpec
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_MonoidHom_exists_galoisCharacter_apply_complexConjugation_eq_apply_frobenius_eq_natCast_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_not_isAbsolutelyIrreducible_of_charpoly_frobenius_eisenstein
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G"

set_option autoImplicit false

noncomputable section

namespace EisAsm

open Polynomial

local notation "Galℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section RankTwo

variable {A : Type*} [CommRing A] [Nontrivial A] {V : Type*} [AddCommGroup V] [Module A V]
  [Module.Free A V] [Module.Finite A V]

theorem charpoly_eq_of_finrank_eq_two (hV : Module.finrank A V = 2) (f : Module.End A V) :
    f.charpoly = X ^ 2 - C (LinearMap.trace A V f) * X + C (LinearMap.det f) := by
  classical
  let b := Module.finBasisOfFinrankEq A V hV
  rw [← LinearMap.charpoly_toMatrix f b, LinearMap.trace_eq_matrix_trace A b, ← LinearMap.det_toMatrix b,
    Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]

theorem trace_eq_of_charpoly_eq (hV : Module.finrank A V = 2) (f : Module.End A V) {t d : A}
    (h : f.charpoly = X ^ 2 - C t * X + C d) : LinearMap.trace A V f = t := by
  have h' := (charpoly_eq_of_finrank_eq_two hV f).symm.trans h
  have := congrArg (fun q : A[X] => q.coeff 1) h'
  simpa [coeff_X, coeff_C, coeff_X_pow] using this

theorem det_eq_of_charpoly_eq (hV : Module.finrank A V = 2) (f : Module.End A V) {t d : A}
    (h : f.charpoly = X ^ 2 - C t * X + C d) : LinearMap.det f = d := by
  have h' := (charpoly_eq_of_finrank_eq_two hV f).symm.trans h
  have := congrArg (fun q : A[X] => q.coeff 0) h'
  simpa [coeff_X, coeff_C, coeff_X_pow] using this

theorem two_mul_det_eq (hV : Module.finrank A V = 2) (f : Module.End A V) :
    2 * LinearMap.det f = LinearMap.trace A V f ^ 2 - LinearMap.trace A V (f * f) := by
  have hCH := LinearMap.aeval_self_charpoly f
  rw [charpoly_eq_of_finrank_eq_two hV f] at hCH
  simp only [map_add, map_sub, map_mul, aeval_X, aeval_C, map_pow, Module.algebraMap_end_eq_smul_id] at hCH
  have h1 : (LinearMap.trace A V f • LinearMap.id * f) = LinearMap.trace A V f • f := by
    rw [smul_mul_assoc, ← Module.End.one_eq_id, one_mul]
  rw [h1] at hCH
  have htr := congrArg (LinearMap.trace A V) hCH
  rw [map_zero, map_add, map_sub, map_smul, map_smul, LinearMap.trace_id, hV] at htr
  simp only [smul_eq_mul, Nat.cast_ofNat] at htr
  rw [pow_two] at htr
  rw [sq]
  linear_combination htr

end RankTwo

theorem charpoly_eq_of_forall_trace_eq {k : Type} [Field k] (h2 : (2 : k) ≠ 0)
    (ρ₁ ρ₂ : ResidualGaloisRep k)
    (h : ∀ σ : Galℚ, LinearMap.trace k ρ₁.V (ρ₁.ρ σ) = LinearMap.trace k ρ₂.V (ρ₂.ρ σ)) (σ : Galℚ) :
    (ρ₁.ρ σ).charpoly = (ρ₂.ρ σ).charpoly := by
  have hd : LinearMap.det (ρ₁.ρ σ) = LinearMap.det (ρ₂.ρ σ) := by
    have e1 := two_mul_det_eq ρ₁.finrank_eq (ρ₁.ρ σ)
    have e2 := two_mul_det_eq ρ₂.finrank_eq (ρ₂.ρ σ)
    rw [← map_mul, h σ, h (σ * σ)] at e1
    rw [← map_mul] at e2
    exact mul_left_cancel₀ h2 (e1.trans e2.symm)
  rw [charpoly_eq_of_finrank_eq_two ρ₁.finrank_eq, charpoly_eq_of_finrank_eq_two ρ₂.finrank_eq, h σ, hd]

section DiagRep

variable {k : Type} [Field k]

def diagHom (χ₁ χ₂ : Galℚ →* kˣ) : Galℚ →* Module.End k (Fin 2 → k) where
  toFun σ := Matrix.toLin' (Matrix.diagonal ![(χ₁ σ : k), (χ₂ σ : k)])
  map_one' := by
    have : (![((χ₁ 1 : kˣ) : k), ((χ₂ 1 : kˣ) : k)] : Fin 2 → k) = fun _ => 1 := by
      ext i; fin_cases i <;> simp
    rw [this]
    show Matrix.toLin' (1 : Matrix (Fin 2) (Fin 2) k) = 1
    exact Matrix.toLin'_one.trans Module.End.one_eq_id.symm
  map_mul' σ τ := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, Matrix.diagonal_mul_diagonal]
    congr 2
    ext i; fin_cases i <;> simp

theorem diagHom_apply (χ₁ χ₂ : Galℚ →* kˣ) (σ : Galℚ) :
    diagHom χ₁ χ₂ σ = Matrix.toLin' (Matrix.diagonal ![(χ₁ σ : k), (χ₂ σ : k)]) := rfl

theorem trace_diagHom (χ₁ χ₂ : Galℚ →* kˣ) (σ : Galℚ) :
    LinearMap.trace k (Fin 2 → k) (diagHom χ₁ χ₂ σ) = (χ₁ σ : k) + (χ₂ σ : k) := by
  rw [diagHom_apply, LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin 2)),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', Matrix.trace_diagonal]
  simp [Fin.sum_univ_two]

theorem det_diagHom (χ₁ χ₂ : Galℚ →* kˣ) (σ : Galℚ) :
    LinearMap.det (diagHom χ₁ χ₂ σ) = (χ₁ σ : k) * (χ₂ σ : k) := by
  rw [diagHom_apply, LinearMap.det_toLin', Matrix.det_diagonal]
  simp [Fin.prod_univ_two]

def diagRep (χ₁ χ₂ : Galℚ →* kˣ) (h₁ : IsOpen ((χ₁.ker : Subgroup Galℚ) : Set Galℚ))
    (h₂ : IsOpen ((χ₂.ker : Subgroup Galℚ) : Set Galℚ)) : ResidualGaloisRep k :=
  { V := Fin 2 → k
    finrank_eq := by simp
    ρ := diagHom χ₁ χ₂
    factorsThroughFiniteLevel := by
      have hopen : IsOpen ((χ₁.ker ⊓ χ₂.ker : Subgroup Galℚ) : Set Galℚ) := IsOpen.inter h₁ h₂
      have hmem : ((χ₁.ker ⊓ χ₂.ker : Subgroup Galℚ) : Set Galℚ) ∈ nhds (1 : Galℚ) :=
        hopen.mem_nhds (Subgroup.one_mem _)
      obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ (AlgebraicClosure ℚ) _).mp hmem
      refine ⟨E, hE, fun σ hσ => ?_⟩
      have hσE : σ ∈ (E.fixingSubgroup : Set Galℚ) := by
        rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]; exact hσ
      have hσker := hsub hσE
      rw [SetLike.mem_coe, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hσker
      show diagHom χ₁ χ₂ σ = 1
      rw [← map_one (diagHom χ₁ χ₂), diagHom_apply, diagHom_apply, hσker.1, hσker.2, map_one, map_one] }

theorem not_isAbsolutelyIrreducible_diagRep (χ₁ χ₂ : Galℚ →* kˣ)
    (h₁ : IsOpen ((χ₁.ker : Subgroup Galℚ) : Set Galℚ))
    (h₂ : IsOpen ((χ₂.ker : Subgroup Galℚ) : Set Galℚ)) :
    ¬ (diagRep χ₁ χ₂ h₁ h₂).IsAbsolutelyIrreducible := by
  intro habs
  rw [ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top] at habs
  change Submodule.span k (Set.range (diagHom χ₁ χ₂ : Galℚ → Module.End k (Fin 2 → k))) = ⊤ at habs

  let Φ : Module.End k (Fin 2 → k) →ₗ[k] k :=
    (LinearMap.proj 0).comp (LinearMap.applyₗ (Pi.single 1 1))
  have hΦ : ∀ f ∈ Submodule.span k (Set.range (diagHom χ₁ χ₂ : Galℚ → Module.End k (Fin 2 → k))),
      Φ f = 0 := by
    intro f hf
    refine Submodule.span_induction (fun g hg => ?_) (map_zero Φ) (fun x y _ _ hx hy => by
      rw [map_add, hx, hy, add_zero]) (fun a x _ hx => by rw [map_smul, hx, smul_zero]) hf
    obtain ⟨σ, rfl⟩ := hg
    show ((diagHom χ₁ χ₂ σ) (Pi.single 1 1)) 0 = 0
    rw [diagHom_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one]
    simp

  let E : Module.End k (Fin 2 → k) := Matrix.toLin' (Matrix.single 0 1 1)
  have hE : Φ E = 1 := by
    show ((Matrix.toLin' (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : k))) (Pi.single 1 1)) 0 = 1
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
    simp
  have hmem : E ∈ Submodule.span k (Set.range (diagHom χ₁ χ₂ : Galℚ → Module.End k (Fin 2 → k))) := by
    rw [habs]; exact Submodule.mem_top
  have := hΦ E hmem
  rw [hE] at this
  exact one_ne_zero this

end DiagRep

theorem main
    {k k' : Type} [Field k] [Field k'] (p : ℕ) [Fact p.Prime] [CharP k' p]
    (ρbar : ResidualGaloisRep k) (ψ : k →+* k')
    (L : ℕ) [NeZero L] (κ : Galℚ →* (ZMod L)ˣ)
    (hκ : ∀ (σ : Galℚ) (μ : AlgebraicClosure ℚ), μ ^ L = 1 → σ μ = μ ^ ((κ σ : ZMod L)).val)
    (c₁ c₂ : (ZMod L)ˣ →* k'ˣ) (h2 : p ≠ 2 ∨ c₁ * c₂ = 1)
    (S₀ : Finset ℕ) (abar : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → k)
    (hρbar : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : Galℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) = X ^ 2 - C (abar ℓ hℓ hℓS) * X + C (ℓ : k))
    (heis : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : Galℚ, A.IsFrobeniusAt σ ℓ →
          ψ (abar ℓ hℓ hℓS) = (c₁ (κ σ) : k') + (ℓ : k') * (c₂ (κ σ) : k')) :
    ¬ ρbar.IsAbsolutelyIrreducible := by
  classical
  intro habs
  have hprime : p.Prime := Fact.out

  let χ₁ : Galℚ →* k'ˣ := c₁.comp κ
  have hκopen := MonoidHom.isOpen_ker_of_cycloCharSpec L κ hκ
  have hχ₁open : IsOpen ((χ₁.ker : Subgroup Galℚ) : Set Galℚ) := by
    refine Subgroup.isOpen_mono (H₁ := κ.ker) (fun x hx => ?_) hκopen
    rw [MonoidHom.mem_ker] at hx ⊢
    show c₁ (κ x) = 1
    rw [hx, map_one]
  obtain ⟨χ₂, hχ₂open, -, hχ₂frob⟩ :=
    MonoidHom.exists_galoisCharacter_apply_complexConjugation_eq_apply_frobenius_eq_natCast_mul
      (k := k') p L c₂
  let ρ' : ResidualGaloisRep k' := diagRep χ₁ χ₂ hχ₁open hχ₂open
  let ρ₂ : ResidualGaloisRep k' := ρbar.baseChangeAlong ψ

  let S₁ : Finset ℕ := insert p S₀ ∪ L.primeFactors
  have hS₁ : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₁ → ℓ ∉ S₀ ∧ ¬ ℓ ∣ L ∧ ℓ ≠ p := by
    intro ℓ hℓ hℓS
    simp only [S₁, Finset.mem_union, Finset.mem_insert, not_or, Nat.mem_primeFactors] at hℓS
    exact ⟨hℓS.1.2, fun h => hℓS.2 ⟨hℓ, h, NeZero.ne L⟩, hℓS.1.1⟩
  have hfrob : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S₁ → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Galℚ),
      A.LiesOverPrime ℓ → A.IsFrobeniusAt τ ℓ →
        LinearMap.trace k' ρ'.V (ρ'.ρ τ) = LinearMap.trace k' ρ₂.V (ρ₂.ρ τ) ∧
        LinearMap.det (ρ'.ρ τ) = (ℓ : k') * ((c₁ * c₂) (κ τ) : k') ∧
        LinearMap.det (ρ₂.ρ τ) = (ℓ : k') := by
    intro ℓ hℓ hℓS A τ hA hτ
    obtain ⟨hℓS₀, hℓL, hℓp⟩ := hS₁ ℓ hℓ hℓS
    have hκτ := ValuationSubring.cycloChar_eq_unitOfCoprime_of_isFrobeniusAt L κ hκ ℓ hℓ hℓL A hA τ hτ
    have hχ₂τ := hχ₂frob ℓ hℓ hℓL hℓp A hA τ hτ
    rw [← hκτ] at hχ₂τ
    have hcp₂ : (ρ₂.ρ τ).charpoly = X ^ 2 - C (ψ (abar ℓ hℓ hℓS₀)) * X + C (ℓ : k') := by
      show ((ρbar.baseChangeAlong ψ).ρ τ).charpoly = _
      rw [ResidualGaloisRep.charpoly_baseChangeAlong, hρbar ℓ hℓ hℓS₀ A hA τ hτ]
      simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_C, map_natCast ψ]
    refine ⟨?_, ?_, det_eq_of_charpoly_eq ρ₂.finrank_eq _ hcp₂⟩
    · rw [trace_eq_of_charpoly_eq ρ₂.finrank_eq _ hcp₂, heis ℓ hℓ hℓS₀ A hA τ hτ]
      show LinearMap.trace k' (Fin 2 → k') (diagHom χ₁ χ₂ τ) = _
      rw [trace_diagHom, show χ₁ τ = c₁ (κ τ) from rfl]
      exact congrArg ((c₁ (κ τ) : k') + ·) hχ₂τ
    · show LinearMap.det (diagHom χ₁ χ₂ τ) = _
      rw [det_diagHom, show χ₁ τ = c₁ (κ τ) from rfl, hχ₂τ, MonoidHom.mul_apply, Units.val_mul]
      exact mul_left_comm _ _ _

  have hcp : ∀ σ : Galℚ, (ρ₂.ρ σ).charpoly = (ρ'.ρ σ).charpoly := by
    rcases h2 with hp2 | h12
    · have h2k : (2 : k') ≠ 0 := by
        rw [Ne, show (2 : k') = ((2 : ℕ) : k') by norm_cast, CharP.cast_eq_zero_iff k' p]
        intro h
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp h)
      have htr : ∀ σ : Galℚ, LinearMap.trace k' ρ₂.V (ρ₂.ρ σ) = LinearMap.trace k' ρ'.V (ρ'.ρ σ) :=
        fun σ => (ResidualGaloisRep.trace_eq_of_trace_frobenius_eq ρ' ρ₂ S₁
          (fun ℓ hℓ hℓS A τ hA hτ => (hfrob ℓ hℓ hℓS A τ hA hτ).1) σ).symm
      exact charpoly_eq_of_forall_trace_eq h2k ρ₂ ρ' htr
    · refine ResidualGaloisRep.charpoly_eq_of_charpoly_frobenius_eq
        (fun M _ _ _ => FrobeniusDensity.statement M) ρ₂ ρ' S₁ ?_
      intro ℓ hℓ hℓS A τ hA hτ
      obtain ⟨htr, hd', hd₂⟩ := hfrob ℓ hℓ hℓS A τ hA hτ
      rw [charpoly_eq_of_finrank_eq_two ρ₂.finrank_eq, charpoly_eq_of_finrank_eq_two ρ'.finrank_eq,
        htr, hd', hd₂, h12, MonoidHom.one_apply, Units.val_one, mul_one]

  have habs₂ : ρ₂.IsAbsolutelyIrreducible := habs.baseChangeAlong ψ
  have habs' : ρ'.IsAbsolutelyIrreducible :=
    ResidualGaloisRep.isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq ρ₂ ρ' habs₂ hcp
  exact not_isAbsolutelyIrreducible_diagRep χ₁ χ₂ hχ₁open hχ₂open habs'

end EisAsm

end

open Polynomial in
theorem solution
    {k k' : Type} [Field k] [Field k'] (p : ℕ) [Fact p.Prime] [CharP k' p]
    (ρbar : ResidualGaloisRep k) (ψ : k →+* k')
    (L : ℕ) [NeZero L] (κ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod L)ˣ)
    (hκ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ L = 1 → σ μ = μ ^ ((κ σ : ZMod L)).val)
    (c₁ c₂ : (ZMod L)ˣ →* k'ˣ) (h2 : p ≠ 2 ∨ c₁ * c₂ = 1)
    (S₀ : Finset ℕ) (abar : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → k)
    (hρbar : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) = X ^ 2 - C (abar ℓ hℓ hℓS) * X + C (ℓ : k))
    (heis : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          ψ (abar ℓ hℓ hℓS) = (c₁ (κ σ) : k') + (ℓ : k') * (c₂ (κ σ) : k')) :
    ¬ ρbar.IsAbsolutelyIrreducible :=
  EisAsm.main p ρbar ψ L κ hκ c₁ c₂ h2 S₀ abar hρbar heis

end S_ResidualGaloisRep_not_isAbsolutelyIrreducible_of_charpoly_frobenius_eisenstein
end P2MW
export P2MW.S_ResidualGaloisRep_not_isAbsolutelyIrreducible_of_charpoly_frobenius_eisenstein (solution)
