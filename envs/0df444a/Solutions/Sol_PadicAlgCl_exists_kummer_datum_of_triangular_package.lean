-- Prove2me | solution 1 for PadicAlgCl.exists_kummer_datum_of_triangular_package
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/5eff5c77-510f-50af-9cb7-6d600a36b1cd

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1_of_level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_exists_kummer_datum_of_triangular_package

set_option autoImplicit false

open groupCohomology groupCohomology.Kummer

local instance ukum_isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

namespace UkumAux

private theorem exists_apply_eq_pow_of_pow_eq_one {K L : Type} [Field K] [Field L] [Algebra K L]
    (n : ℕ) [NeZero n] (g : L ≃ₐ[K] L) :
    ∃ a : ℕ, ∀ μ : L, μ ^ n = 1 → g μ = μ ^ a := by
  refine ⟨(modularCyclotomicCharacter.toFun n g.toRingEquiv).val, fun μ hμ => ?_⟩
  have h := modularCyclotomicCharacter.toFun_spec g.toRingEquiv (rootsOfUnity.mkOfPowEq μ hμ)
  simpa [Units.val_pow_eq_pow_val, rootsOfUnity.val_mkOfPowEq_coe] using h

private theorem pow_val_eq {M : Type} [Monoid M] {ζ : M} {p : ℕ} [NeZero p] (hζ : ζ ^ p = 1)
    (u : ZMod p) (m : ℕ) (h : (m : ZMod p) = u) : ζ ^ u.val = ζ ^ m := by
  rw [← h, ZMod.val_natCast, ← pow_eq_pow_mod m hζ]

private theorem exists_local_level (p : ℕ) [Fact p.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : FiniteDimensional ℚ F) :
    ∃ E : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] E ∧
      ∀ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, τ ∈ E.fixingSubgroup →
        localGaloisToGlobal p τ ∈ F.fixingSubgroup := by
  classical
  haveI := hF
  letI : IsScalarTower ℚ ℚ_[p] (PadicAlgCl p) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  obtain ⟨T, hT⟩ : F.FG :=
    F.fg_of_fg_toSubalgebra (Subalgebra.fg_of_fg_toSubmodule (Module.Finite.iff_fg.mp hF))
  refine ⟨IntermediateField.adjoin ℚ_[p] (padicEmbedding p '' (↑T : Set (AlgebraicClosure ℚ))),
    ?_, ?_⟩
  · haveI : Finite ↥(padicEmbedding p '' (↑T : Set (AlgebraicClosure ℚ))) :=
      (T.finite_toSet.image _).to_subtype
    refine IntermediateField.finiteDimensional_adjoin fun v hv => ?_
    obtain ⟨w, -, rfl⟩ := hv
    have hw : IsIntegral ℚ w := (Algebra.IsAlgebraic.isAlgebraic w).isIntegral
    exact (hw.map (padicEmbedding p)).tower_top
  · intro τ hτ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ ⊢
    intro w hw
    apply (padicEmbedding p).toRingHom.injective
    show padicEmbedding p (localGaloisToGlobal p τ w) = padicEmbedding p w
    rw [padicEmbedding_localGaloisToGlobal]
    apply hτ
    have h1 : padicEmbedding p w ∈
        (IntermediateField.adjoin ℚ (↑T : Set (AlgebraicClosure ℚ))).map (padicEmbedding p) := by
      rw [hT]
      exact (IntermediateField.mem_map _).mpr ⟨w, hw, rfl⟩
    rw [IntermediateField.adjoin_map] at h1
    have h2 : IntermediateField.adjoin ℚ (padicEmbedding p '' (↑T : Set (AlgebraicClosure ℚ))) ≤
        (IntermediateField.adjoin ℚ_[p]
          (padicEmbedding p '' (↑T : Set (AlgebraicClosure ℚ)))).restrictScalars ℚ :=
      IntermediateField.adjoin_le_iff.mpr fun v hv =>
        (IntermediateField.mem_restrictScalars ℚ).mpr (IntermediateField.subset_adjoin _ _ hv)
    exact (IntermediateField.mem_restrictScalars ℚ).mp (h2 h1)

end UkumAux

theorem solution
    {B : Type} [CommRing B] [IsLocalRing B] (p : ℕ) [Fact p.Prime]
    (hpB : (p : B) ∈ IsLocalRing.maximalIdeal B)
    (x z : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → Bˣ) (y : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → B)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : FiniteDimensional ℚ F)
    (hxmul : ∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), x (g * h) = x g * x h)
    (hzmul : ∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), z (g * h) = z g * z h)
    (hy : ∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), y (g * h) = (x g : B) * y h + y g * (z h : B))
    (hlev : ∀ s : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), localGaloisToGlobal p s ∈ F.fixingSubgroup → x s = 1 ∧ y s = 0 ∧ z s = 1)
    (hcyc : ∀ (g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (n a : ℕ), (∀ μ : PadicAlgCl p, μ ^ p ^ n = 1 → g μ = μ ^ a) →
      (x g : B) * (z g : B) - (a : B) ∈ Ideal.span {((p ^ n : ℕ) : B)})
    (hzsq : ∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (z g : B) * (z g : B) - 1 ∈ IsLocalRing.maximalIdeal B)
    (ζ : PadicAlgCl p) (hζ : IsPrimitiveRoot ζ p)
    (Λ : IsLocalRing.ResidueField B →+ ZMod p) (η : B) :
    ∃ (a : ℚ_[p]ˣ) (α : (PadicAlgCl p)ˣ),
      algebraMap ℚ_[p] (PadicAlgCl p) (a : ℚ_[p]) = (α : PadicAlgCl p) ^ p ∧
      ∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), g (α : PadicAlgCl p) =
          ζ ^ (Λ (IsLocalRing.residue B (η * (y g * (((z g)⁻¹ : Bˣ) : B))))).val * (α : PadicAlgCl p) := by
  classical
  have _hxmul := hxmul
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  let c : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → B := fun g => y g * (((z g)⁻¹ : Bˣ) : B)
  let Eχ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → ZMod p := fun g =>
    Λ (IsLocalRing.residue B (η * c g))

  let ζu : (PadicAlgCl p)ˣ := (hζ.isUnit hp.ne_zero).unit
  have hζu : (ζu : PadicAlgCl p) = ζ := (hζ.isUnit hp.ne_zero).unit_spec
  have hζup : ζu ^ p = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, hζu, hζ.pow_eq_one, Units.val_one])
  let f : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → (PadicAlgCl p)ˣ := fun g => ζu ^ (Eχ g).val
  have hfval : ∀ g, (f g : PadicAlgCl p) = ζ ^ (Eχ g).val := fun g => by
    show ((ζu ^ (Eχ g).val : (PadicAlgCl p)ˣ) : PadicAlgCl p) = _
    rw [Units.val_pow_eq_pow_val, hζu]

  have hc : ∀ g h, c (g * h) = (x g : B) * (((z g)⁻¹ : Bˣ) : B) * c h + c g := by
    intro g h
    show y (g * h) * (((z (g * h))⁻¹ : Bˣ) : B) =
      (x g : B) * (((z g)⁻¹ : Bˣ) : B) * (y h * (((z h)⁻¹ : Bˣ) : B)) + y g * (((z g)⁻¹ : Bˣ) : B)
    have hzh : (z h : B) * (((z h)⁻¹ : Bˣ) : B) = 1 := Units.mul_inv (z h)
    rw [hy, hzmul, mul_inv, Units.val_mul]
    linear_combination (y g * (((z g)⁻¹ : Bˣ) : B)) * hzh

  have hxw : ∀ (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (a : ℕ),
      (∀ μ : PadicAlgCl p, μ ^ p = 1 → g μ = μ ^ a) →
      IsLocalRing.residue B ((x g : B) * (((z g)⁻¹ : Bˣ) : B)) =
        (a : IsLocalRing.ResidueField B) := by
    intro g a ha
    have h1 : (x g : B) * (z g : B) - (a : B) ∈ IsLocalRing.maximalIdeal B := by
      have := hcyc g 1 a (fun μ hμ => ha μ (by rwa [pow_one] at hμ))
      refine (Ideal.span_le.mpr ?_) this
      rw [Set.singleton_subset_iff, pow_one]
      exact hpB
    have h2 : (x g : B) * (((z g)⁻¹ : Bˣ) : B) - (x g : B) * (z g : B) ∈
        IsLocalRing.maximalIdeal B := by
      have hzg : (z g : B) * (((z g)⁻¹ : Bˣ) : B) = 1 := Units.mul_inv (z g)
      have : (x g : B) * (((z g)⁻¹ : Bˣ) : B) - (x g : B) * (z g : B) =
          -((x g : B) * (((z g)⁻¹ : Bˣ) : B)) * ((z g : B) * (z g : B) - 1) := by
        linear_combination ((x g : B) * (z g : B)) * hzg
      rw [this]
      exact Ideal.mul_mem_left _ _ (hzsq g)
    rw [← sub_eq_zero, ← map_natCast (IsLocalRing.residue B) a, ← map_sub,
      IsLocalRing.residue_eq_zero_iff]
    have := Ideal.add_mem _ h2 h1
    rwa [sub_add_sub_cancel] at this

  have hE : ∀ (g h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (a : ℕ),
      (∀ μ : PadicAlgCl p, μ ^ p = 1 → g μ = μ ^ a) →
      Eχ (g * h) = (a : ZMod p) * Eχ h + Eχ g := by
    intro g h a ha
    show Λ (IsLocalRing.residue B (η * c (g * h))) =
      (a : ZMod p) * Λ (IsLocalRing.residue B (η * c h)) + Λ (IsLocalRing.residue B (η * c g))
    have key : IsLocalRing.residue B (η * ((x g : B) * (((z g)⁻¹ : Bˣ) : B) * c h + c g)) =
        (a : IsLocalRing.ResidueField B) * IsLocalRing.residue B (η * c h) +
          IsLocalRing.residue B (η * c g) := by
      simp only [map_add, map_mul, hxw g a ha]
      ring
    rw [hc, key, map_add, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]

  have hcoc : IsMulCocycle₁ f := by
    intro g h
    obtain ⟨a, ha⟩ := UkumAux.exists_apply_eq_pow_of_pow_eq_one p g
    apply Units.ext
    rw [Units.val_mul, val_smul_units (K := ℚ_[p]), hfval, hfval, hfval, map_pow,
      ha ζ hζ.pow_eq_one, ← pow_mul, ← pow_add, hE g h a ha]
    exact UkumAux.pow_val_eq hζ.pow_eq_one _ _
      (by simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val])
  have hfp : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, f σ ^ p = 1 := fun σ => by
    show (ζu ^ (Eχ σ).val) ^ p = 1
    rw [← pow_mul, mul_comm, pow_mul, hζup, one_pow]

  obtain ⟨E, hEfd, hEfix⟩ := UkumAux.exists_local_level p F hF
  have hlc : ∃ E : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] E ∧
      ∀ σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, τ ∈ E.fixingSubgroup → f (σ * τ) = f σ := by
    refine ⟨E, hEfd, fun σ τ hτ => ?_⟩
    obtain ⟨-, hy0, hz1⟩ := hlev τ (hEfix τ hτ)
    have hcc : c (σ * τ) = c σ := by
      show y (σ * τ) * (((z (σ * τ))⁻¹ : Bˣ) : B) = y σ * (((z σ)⁻¹ : Bˣ) : B)
      rw [hy, hzmul, hy0, hz1]
      simp only [mul_zero, zero_add, Units.val_one, mul_one]
    show ζu ^ (Λ (IsLocalRing.residue B (η * c (σ * τ)))).val =
      ζu ^ (Λ (IsLocalRing.residue B (η * c σ))).val
    rw [hcc]

  obtain ⟨a, α, hα, hfα⟩ := exists_kummerCocycle_eq_of_isMulCocycle1_of_level hcoc hfp hlc
  refine ⟨a, α, hα, fun g => ?_⟩
  have h := hfα g
  rw [kummerCocycle_apply, eq_comm, div_eq_iff_eq_mul] at h
  have h' := congrArg Units.val h
  rw [val_smul_units, Units.val_mul, hfval] at h'
  exact h'

end S_PadicAlgCl_exists_kummer_datum_of_triangular_package
end P2MW
export P2MW.S_PadicAlgCl_exists_kummer_datum_of_triangular_package (solution)
