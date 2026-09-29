-- Prove2me | solution 1 for ValuationSubring.tameCharacter_eq_one_iff_apply_eq_and_conj_mem_and_exists_apply_eq_of_pow_sq_sub_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8ac0037e-c334-5cd6-9fc3-4701716aad1c

import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_tameCharacter_eq_one_iff_apply_eq_and_conj_mem_and_exists_apply_eq_of_pow_sq_sub_one_eq

set_option autoImplicit false

namespace TameCharLevelTwoEngine

open IsLocalRing Polynomial

theorem valuation_eq_one_of_pow_eq_one {L : Type*} [Field L] (A : ValuationSubring L)
    {ζ : L} {m : ℕ} (hm : m ≠ 0) (hζ : ζ ^ m = 1) : A.valuation ζ = 1 := by
  have h : A.valuation ζ ^ m = 1 := by rw [← map_pow, hζ, map_one]
  exact (pow_eq_one_iff_of_nonneg zero_le' hm).mp h

theorem mem_of_pow_eq_one {L : Type*} [Field L] (A : ValuationSubring L)
    {ζ : L} {m : ℕ} (hm : m ≠ 0) (hζ : ζ ^ m = 1) : ζ ∈ A :=
  (A.valuation_le_one_iff ζ).mp (valuation_eq_one_of_pow_eq_one A hm hζ).le

theorem eq_one_of_pow_eq_one_of_residue_eq_one {R : Type*} [CommRing R] [IsLocalRing R]
    {u : R} {m : ℕ} (hu : u ^ m = 1) (hm : ((m : ℕ) : ResidueField R) ≠ 0)
    (h1 : residue R u = 1) : u = 1 := by

  have hgeom : (u - 1) * (Finset.range m).sum (fun i => u ^ i) = 0 := by
    rw [mul_geom_sum, hu, sub_self]

  have hunit : IsUnit ((Finset.range m).sum (fun i => u ^ i)) := by
    rw [← residue_ne_zero_iff_isUnit]
    rw [map_sum]
    simp only [map_pow, h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact hm
  have h0 : u - 1 = 0 := (hunit.mul_left_eq_zero).mp hgeom
  exact sub_eq_zero.mp h0

theorem eq_one_of_pow_eq_one_of_valuation_sub_one_lt_one {L : Type*} [Field L]
    (A : ValuationSubring L) {η : L} {m : ℕ} (hm : m ≠ 0) (hη : η ^ m = 1)
    (hmk : ((m : ℕ) : ResidueField A) ≠ 0) (hv : A.valuation (η - 1) < 1) : η = 1 := by
  have hηA : η ∈ A := mem_of_pow_eq_one A hm hη
  set u : A := ⟨η, hηA⟩ with hu_def
  have hu : u ^ m = 1 := by
    apply Subtype.ext
    simp [hu_def, hη]
  have hmax : u - 1 ∈ maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    simpa [hu_def] using hv
  have h1 : residue A u = 1 := by
    have : residue A (u - 1) = 0 := (residue_eq_zero_iff _).mpr hmax
    rwa [map_sub, map_one, sub_eq_zero] at this
  have := eq_one_of_pow_eq_one_of_residue_eq_one hu hmk h1
  have := congrArg (fun x : A => (x : L)) this
  simpa [hu_def] using this

theorem valuation_sub_lt_one_of_mem_inertiaSubgroupIn {K L : Type*} [Field K] [Field L]
    [Algebra K L] (A : ValuationSubring L) {τ : L ≃ₐ[K] L} (hτ : τ ∈ A.inertiaSubgroupIn K)
    {x : L} (hx : x ∈ A) : ∃ _ : τ x ∈ A, A.valuation (τ x - x) < 1 := by
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hτ
  have htA : ((t : L ≃ₐ[K] L) x) ∈ A := by
    have := (t • (⟨x, hx⟩ : A)).2
    exact this
  refine ⟨htA, ?_⟩

  have hker : MulSemiringAction.toRingAut (A.decompositionSubgroup K) (ResidueField A) t = 1 :=
    (MonoidHom.mem_ker).mp ht
  have hres : residue A (t • (⟨x, hx⟩ : A)) = residue A ⟨x, hx⟩ := by
    rw [ResidueField.residue_smul]
    have := RingEquiv.congr_fun hker (residue A ⟨x, hx⟩)
    simpa using this
  have hmax : t • (⟨x, hx⟩ : A) - ⟨x, hx⟩ ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff, map_sub, hres, sub_self]
  have := (ValuationSubring.valuation_lt_one_iff _ _).mp hmax
  exact this

theorem apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn {K L : Type*} [Field K] [Field L]
    [Algebra K L] (A : ValuationSubring L) {τ : L ≃ₐ[K] L} (hτ : τ ∈ A.inertiaSubgroupIn K)
    {ξ : L} {m : ℕ} (hm : m ≠ 0) (hξ : ξ ^ m = 1) (hmk : ((m : ℕ) : ResidueField A) ≠ 0) :
    τ ξ = ξ := by
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [zero_pow hm] at hξ
    exact zero_ne_one hξ
  have hξA : ξ ∈ A := mem_of_pow_eq_one A hm hξ
  obtain ⟨-, hv⟩ := valuation_sub_lt_one_of_mem_inertiaSubgroupIn A hτ hξA

  have hη : (τ ξ / ξ) ^ m = 1 := by
    rw [div_pow, ← map_pow, hξ, map_one, one_div_one]
  have hvξ : A.valuation ξ = 1 := valuation_eq_one_of_pow_eq_one A hm hξ
  have hv' : A.valuation (τ ξ / ξ - 1) < 1 := by
    have : τ ξ / ξ - 1 = (τ ξ - ξ) / ξ := by field_simp
    rw [this, map_div₀, hvξ, div_one]
    exact hv
  have := eq_one_of_pow_eq_one_of_valuation_sub_one_lt_one A hm hη hmk hv'
  rwa [div_eq_one_iff_eq hξ0] at this

theorem conj_mem_inertiaSubgroupIn {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) {σ τ : L ≃ₐ[K] L} (hσ : σ ∈ A.decompositionSubgroup K)
    (hτ : τ ∈ A.inertiaSubgroupIn K) : σ * τ * σ⁻¹ ∈ A.inertiaSubgroupIn K := by
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hτ
  have hN : (A.inertiaSubgroup K).Normal := MonoidHom.normal_ker _
  have hmem : (⟨σ, hσ⟩ : A.decompositionSubgroup K) * t * (⟨σ, hσ⟩)⁻¹ ∈ A.inertiaSubgroup K :=
    hN.conj_mem t ht ⟨σ, hσ⟩
  exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩

theorem residue_natCast_eq_zero_of_liesOverPrime {L : Type*} [Field L] (A : ValuationSubring L)
    {q : ℕ} (hA : A.LiesOverPrime q) : ((q : ℕ) : ResidueField A) = 0 := by
  have h1 : ((q : A) : L) ∈ A.nonunits := by
    have : ((q : A) : L) = (q : L) := by simp
    rw [this]; exact hA
  have h2 : (q : A) ∈ maximalIdeal A := ValuationSubring.coe_mem_nonunits_iff.mp h1
  have h3 : residue A (q : A) = 0 := (residue_eq_zero_iff _).mpr h2
  simpa using h3

theorem natCast_sq_sub_one_ne_zero_of_liesOverPrime {L : Type*} [Field L]
    (A : ValuationSubring L) {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q) :
    ((q ^ 2 - 1 : ℕ) : ResidueField A) ≠ 0 := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq.pos
  rw [Nat.cast_sub h1, Nat.cast_pow, residue_natCast_eq_zero_of_liesOverPrime A hA]
  simp

theorem exists_apply_eq_of_pow_sq_eq (q : ℕ) [hq : Fact q.Prime] {k : Type*} [Field k]
    (ι : GaloisField q 2 →+* k) {v : k} (hv : v ^ (q ^ 2) = v) :
    ∃ α : GaloisField q 2, ι α = v := by
  classical
  letI : Fintype (GaloisField q 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField q 2) = q ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card q 2 two_ne_zero
  have hq1 : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero hq.out.one_lt
  set f : k[X] := X ^ (q ^ 2) - X with hf_def
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hq1
  have hfdeg : f.natDegree = q ^ 2 := FiniteField.X_pow_card_sub_X_natDegree_eq k hq1
  set S : Finset k := Finset.univ.image ι with hS_def
  have hScard : S.card = q ^ 2 := by
    rw [hS_def, Finset.card_image_of_injective _ ι.injective, Finset.card_univ, hcard]
  have hsub : S ⊆ f.roots.toFinset := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
    rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot.def, hf_def, eval_sub, eval_pow, eval_X,
      ← map_pow, ← hcard, FiniteField.pow_card, sub_self]
  have hle : f.roots.toFinset.card ≤ S.card := by
    rw [hScard, ← hfdeg]
    exact (Multiset.toFinset_card_le _).trans (card_roots' f)
  have hSeq : S = f.roots.toFinset := Finset.eq_of_subset_of_card_le hsub hle
  have hvmem : v ∈ f.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot.def, hf_def, eval_sub, eval_pow, eval_X, hv,
      sub_self]
  rw [← hSeq, hS_def, Finset.mem_image] at hvmem
  obtain ⟨α, -, hα⟩ := hvmem
  exact ⟨α, hα⟩

section Main

variable (q : ℕ) [hq : Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ))
  (hP : P.LiesOverPrime q) (π : AlgebraicClosure ℚ)
  (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))

theorem sq_sub_one_ne_zero : q ^ 2 - 1 ≠ 0 :=
  Nat.sub_ne_zero_of_lt (Nat.one_lt_pow two_ne_zero hq.out.one_lt)

include hπ in
theorem pi_ne_zero : π ≠ 0 := by
  intro h
  rw [h, zero_pow (sq_sub_one_ne_zero q)] at hπ
  exact (Nat.cast_ne_zero.mpr hq.out.ne_zero) hπ.symm

include hπ in

theorem div_pow_eq_one (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (τ π / π) ^ (q ^ 2 - 1) = 1 := by
  have h0 : (π : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) ≠ 0 := by
    rw [hπ]; exact Nat.cast_ne_zero.mpr hq.out.ne_zero
  rw [div_pow, ← map_pow, hπ, map_natCast, ← hπ, div_self h0]

include hπ in
theorem div_mem (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : τ π / π ∈ P :=
  mem_of_pow_eq_one P (sq_sub_one_ne_zero q) (div_pow_eq_one q π hπ τ)

include hπ in

theorem tameCharacter_eq (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    P.tameCharacter π τ = residue P ⟨τ π / π, div_mem q P π hπ τ⟩ := by
  unfold ValuationSubring.tameCharacter
  rw [dif_pos (div_mem q P π hπ τ)]

include hP hπ in

theorem tameCharacter_eq_one_iff (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    P.tameCharacter π τ = 1 ↔ τ π = π := by
  have hπ0 := pi_ne_zero q π hπ
  rw [tameCharacter_eq q P π hπ τ]
  constructor
  · intro h
    have h1 : residue P (⟨τ π / π, div_mem q P π hπ τ⟩ - 1) = 0 := by
      rw [map_sub, h, map_one, sub_self]
    have h2 := (residue_eq_zero_iff _).mp h1
    have h3 : P.valuation (τ π / π - 1) < 1 := by
      have := (ValuationSubring.valuation_lt_one_iff _ _).mp h2
      simpa using this
    have h4 := eq_one_of_pow_eq_one_of_valuation_sub_one_lt_one P (sq_sub_one_ne_zero q)
      (div_pow_eq_one q π hπ τ) (natCast_sq_sub_one_ne_zero_of_liesOverPrime P hq.out hP) h3
    rwa [div_eq_one_iff_eq hπ0] at h4
  · intro h
    have : (⟨τ π / π, div_mem q P π hπ τ⟩ : P) = 1 := by
      apply Subtype.ext
      simp [h, hπ0]
    rw [this, map_one]

include hP hπ in

theorem conj_apply_eq (σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hτ : τ ∈ P.inertiaSubgroupIn ℚ) (hτπ : τ π = π) : (σ * τ * σ⁻¹) π = π := by
  have hπ0 := pi_ne_zero q π hπ

  have hξ : (σ⁻¹ π / π) ^ (q ^ 2 - 1) = 1 := div_pow_eq_one q π hπ σ⁻¹
  have hτξ : τ (σ⁻¹ π / π) = σ⁻¹ π / π :=
    apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn P hτ (sq_sub_one_ne_zero q) hξ
      (natCast_sq_sub_one_ne_zero_of_liesOverPrime P hq.out hP)
  have hdecomp : σ⁻¹ π = (σ⁻¹ π / π) * π := by rw [div_mul_cancel₀ _ hπ0]
  have hτσ : τ (σ⁻¹ π) = σ⁻¹ π := by
    conv_lhs => rw [hdecomp, map_mul, hτξ, hτπ]
    exact hdecomp.symm
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτσ]
  exact σ.apply_symm_apply π

include hπ in

theorem tameCharacter_pow_sq (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    P.tameCharacter π τ ^ (q ^ 2) = P.tameCharacter π τ := by
  have h1 : P.tameCharacter π τ ^ (q ^ 2 - 1) = 1 := by
    rw [tameCharacter_eq q P π hπ τ, ← map_pow]
    have : (⟨τ π / π, div_mem q P π hπ τ⟩ : P) ^ (q ^ 2 - 1) = 1 := by
      apply Subtype.ext
      simp [div_pow_eq_one q π hπ τ]
    rw [this, map_one]
  have h2 : q ^ 2 = (q ^ 2 - 1) + 1 :=
    (Nat.sub_add_cancel (Nat.one_le_pow _ _ hq.out.pos)).symm
  rw [h2, pow_succ, h1, one_mul]

end Main

end TameCharLevelTwoEngine

open TameCharLevelTwoEngine in
theorem solution
    (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) :
    (∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.tameCharacter π τ = 1 ↔ τ π = π) ∧
    (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π τ = 1 →
      σ * τ * σ⁻¹ ∈ P.inertiaSubgroupIn ℚ ∧ P.tameCharacter π (σ * τ * σ⁻¹) = 1) ∧
    (∀ ι : GaloisField q 2 →+* IsLocalRing.ResidueField P,
      ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∃ α : GaloisField q 2, ι α = P.tameCharacter π τ) := by
  refine ⟨fun τ => tameCharacter_eq_one_iff q P hP π hπ τ, ?_, ?_⟩
  · intro σ hσ τ hτ h1
    refine ⟨conj_mem_inertiaSubgroupIn P hσ hτ, ?_⟩
    rw [tameCharacter_eq_one_iff q P hP π hπ] at h1 ⊢
    exact conj_apply_eq q P hP π hπ σ τ hτ h1
  · intro ι τ
    exact exists_apply_eq_of_pow_sq_eq q ι (tameCharacter_pow_sq q P π hπ τ)

end S_ValuationSubring_tameCharacter_eq_one_iff_apply_eq_and_conj_mem_and_exists_apply_eq_of_pow_sq_sub_one_eq
end P2MW
export P2MW.S_ValuationSubring_tameCharacter_eq_one_iff_apply_eq_and_conj_mem_and_exists_apply_eq_of_pow_sq_sub_one_eq (solution)
