-- Prove2me | solution 1 for ValuationSubring.exists_tame_generator_inertiaSubgroupIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/bf041fcc-c10f-57b3-99e0-e8e9abaac1e4

import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.KummerExtension
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Int.GCD
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_tame_generator_inertiaSubgroupIn

set_option autoImplicit false

section
open GaloisRep Finset IsLocalRing

namespace WCOTTameR

theorem eq_of_pow_eq_one_of_sub_mem {R : Type} [CommRing R] [IsLocalRing R] {m : ℕ} (hm : m ≠ 0)
    (hmu : IsUnit ((m : ℕ) : R)) (x y : R) (hx : x ^ m = 1) (hy : y ^ m = 1)
    (hxy : x - y ∈ IsLocalRing.maximalIdeal R) : x = y := by
  have htel : (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) * (x - y) = 0 := by
    rw [geom_sum₂_mul, hx, hy, sub_self]
  have hres : IsLocalRing.residue R x = IsLocalRing.residue R y := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hxy
  have hyu : IsUnit y := IsUnit.of_pow_eq_one hy hm
  have hS : IsUnit (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]
    have hr : IsLocalRing.residue R (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) =
        (m : IsLocalRing.ResidueField R) * IsLocalRing.residue R y ^ (m - 1) := by
      rw [map_sum]
      simp only [map_mul, map_pow, hres]
      exact geom_sum₂_self _ _
    rw [hr]
    have h1 : IsUnit (m : IsLocalRing.ResidueField R) := by
      simpa using hmu.map (IsLocalRing.residue R)
    exact (h1.mul ((hyu.map (IsLocalRing.residue R)).pow (m - 1))).ne_zero
  exact sub_eq_zero.mp ((hS.mul_right_eq_zero).mp htel)

variable {L : Type} [Field L]

theorem mem_of_pow_eq_one (A : ValuationSubring L) {μ : L} {m : ℕ} (hm : m ≠ 0) (hμ : μ ^ m = 1) :
    μ ∈ A := by
  rcases A.mem_or_inv_mem μ with h | h
  · exact h
  · have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_pow hm] at hμ
      exact zero_ne_one hμ
    have h1 : μ ^ (m - 1) = μ⁻¹ := by
      rw [pow_sub₀ μ hμ0 (Nat.one_le_iff_ne_zero.mpr hm), hμ, pow_one, one_mul]
    have h2 : μ = μ⁻¹ ^ (m - 1) := by rw [inv_pow, h1, inv_inv]
    rw [h2]
    exact pow_mem h _

theorem isUnit_natCast_of_coprime (A : ValuationSubring L) {q m : ℕ} (hq : A.LiesOverPrime q)
    (hmq : Nat.Coprime m q) : IsUnit ((m : ℕ) : A) := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hm
  have hqA : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    first | exact hq | simpa using hq
  obtain ⟨u, v, huv⟩ := (Nat.Coprime.cast (R := A) hmq)
  have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← huv]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hqA)
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

variable {K : Type} [Field K] [Algebra K L]

theorem inertia_fixes_root_of_unity (A : ValuationSubring L) {q : ℕ} (hq : A.LiesOverPrime q)
    {m : ℕ} (hm : m ≠ 0) (hmq : Nat.Coprime m q) (μ : L) (hμ : μ ^ m = 1)
    (σ : L ≃ₐ[K] L) (hσ : σ ∈ A.inertiaSubgroupIn K) : σ μ = μ := by

  obtain ⟨τ, hτI, hτσ⟩ := hσ
  subst hτσ

  have hμA : μ ∈ A := mem_of_pow_eq_one A hm hμ
  have hτμ : ((τ : L ≃ₐ[K] L) μ) ^ m = 1 := by rw [← map_pow, hμ, map_one]
  have hτμA : (τ : L ≃ₐ[K] L) μ ∈ A := mem_of_pow_eq_one A hm hτμ
  set x : A := ⟨(τ : L ≃ₐ[K] L) μ, hτμA⟩
  set y : A := ⟨μ, hμA⟩
  have hx : x ^ m = 1 := Subtype.ext (by
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hτμ)
  have hy : y ^ m = 1 := Subtype.ext (by
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hμ)

  have hτy : τ • y = x := rfl
  have hres : IsLocalRing.residue A x = IsLocalRing.residue A y := by
    rw [← hτy, IsLocalRing.ResidueField.residue_smul]
    have hτker : MulSemiringAction.toRingAut (A.decompositionSubgroup K)
        (IsLocalRing.ResidueField A) τ = 1 := hτI
    have := DFunLike.congr_fun (congrArg RingEquiv.toEquiv hτker) (IsLocalRing.residue A y)
    simpa using this
  have hxy : x - y ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hres, sub_self]
  have key := eq_of_pow_eq_one_of_sub_mem hm (isUnit_natCast_of_coprime A hq hmq) x y hx hy hxy
  exact congrArg Subtype.val key

theorem apply_eq_pow_of_isFrobeniusAt (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (q : ℕ)
    (hσ : A.IsFrobeniusAt σ q) (hq : A.LiesOverPrime q) {m : ℕ} (hm : m ≠ 0) (hmq : Nat.Coprime m q)
    (μ : L) (hμ : μ ^ m = 1) : σ μ = μ ^ q := by
  obtain ⟨hσD, hfrob⟩ := hσ
  have hμA : μ ∈ A := mem_of_pow_eq_one A hm hμ
  have hσμ : (σ μ) ^ m = 1 := by rw [← map_pow, hμ, map_one]
  have hσμA : σ μ ∈ A := mem_of_pow_eq_one A hm hσμ
  have hx : (⟨σ μ, hσμA⟩ : A) ^ m = 1 := Subtype.ext (by
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hσμ)
  have hy : ((⟨μ, hμA⟩ : A) ^ q) ^ m = 1 := Subtype.ext (by
    rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, OneMemClass.coe_one, ← pow_mul, mul_comm, pow_mul]
    change (μ ^ m) ^ q = 1
    rw [hμ, one_pow])
  have hsmul : ((⟨σ, hσD⟩ : A.decompositionSubgroup K) • (⟨μ, hμA⟩ : A)) = ⟨σ μ, hσμA⟩ :=
    Subtype.ext rfl
  have hxy : (⟨σ μ, hσμA⟩ : A) - (⟨μ, hμA⟩ : A) ^ q ∈ IsLocalRing.maximalIdeal A := by
    have h1 := hfrob (IsLocalRing.residue A ⟨μ, hμA⟩)
    rw [← IsLocalRing.ResidueField.residue_smul, hsmul, ← map_pow] at h1
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact h1
  have key := eq_of_pow_eq_one_of_sub_mem hm (isUnit_natCast_of_coprime A hq hmq) _ _ hx hy hxy
  have := congrArg Subtype.val key
  simpa using this

theorem kummer_cocycle_eq (τ : L ≃ₐ[K] L) {m : ℕ}
    (hτμ : ∀ ζ : L, ζ ^ m = 1 → τ ζ = ζ) (c : L)
    (α β : L) (hα : α ^ m = c) (hβ : β ^ m = c) (hα0 : α ≠ 0) (hβ0 : β ≠ 0) :
    τ α / α = τ β / β := by
  have hc0 : c ≠ 0 := by rw [← hα]; exact pow_ne_zero m hα0
  have hζ : (β / α) ^ m = 1 := by rw [div_pow, hα, hβ, div_self hc0]
  have key : τ β = (β / α) * τ α := by
    conv_lhs => rw [← div_mul_cancel₀ β hα0, map_mul, hτμ _ hζ]
  rw [key]; field_simp

theorem apply_pow_eq_cocycle_pow_mul (τ : L ≃ₐ[K] L) {m : ℕ}
    (hτμ : ∀ ζ : L, ζ ^ m = 1 → τ ζ = ζ) (α : L) (hα0 : α ≠ 0)
    (hcocycle : (τ α / α) ^ m = 1) :
    ∀ n : ℕ, (τ ^ n) α = (τ α / α) ^ n * α := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hτμ _ hcocycle, pow_succ, mul_assoc]
    congr 1
    rw [div_mul_cancel₀ _ hα0]

theorem frob_conj_eq_pow_on_radical (A : ValuationSubring L) {q : ℕ} (hq : A.LiesOverPrime q)
    {m : ℕ} (hm : m ≠ 0) (hmq : Nat.Coprime m q)
    (τ : L ≃ₐ[K] L) (hτ : τ ∈ A.inertiaSubgroupIn K)
    (σ : L ≃ₐ[K] L) (hσ : A.IsFrobeniusAt σ q)
    (α : L) (hα : α ^ m = (q : L)) (hα0 : α ≠ 0) :
    (σ * τ * σ⁻¹) α = (τ ^ q) α := by

  have hτμ : ∀ ζ : L, ζ ^ m = 1 → τ ζ = ζ :=
    fun ζ hζ => inertia_fixes_root_of_unity A hq hm hmq ζ hζ τ hτ

  have hσμ : ∀ ζ : L, ζ ^ m = 1 → σ ζ = ζ ^ q :=
    fun ζ hζ => apply_eq_pow_of_isFrobeniusAt A σ q hσ hq hm hmq ζ hζ

  have hq0 : (q : L) ≠ 0 := hα ▸ pow_ne_zero m hα0

  have hτqL : τ ((q : L)) = q := map_natCast τ q

  set χ := τ α / α with hχdef
  have hχm : χ ^ m = 1 := by
    rw [hχdef, div_pow, ← map_pow, hα, hτqL, div_self hq0]

  have hRHS : (τ ^ q) α = χ ^ q * α := apply_pow_eq_cocycle_pow_mul τ hτμ α hα0 hχm q

  have hLHS : (σ * τ * σ⁻¹) α = χ ^ q * α := by
    have hβm : (σ⁻¹ α) ^ m = (q : L) := by
      rw [← map_pow, hα]; exact map_natCast σ⁻¹ q
    have hβ0 : σ⁻¹ α ≠ 0 := by
      simp only [ne_eq, AddEquivClass.map_eq_zero_iff]; exact hα0
    have hcoc : τ α / α = τ (σ⁻¹ α) / (σ⁻¹ α) :=
      kummer_cocycle_eq τ hτμ (q : L) α (σ⁻¹ α) hα hβm hα0 hβ0
    have key : τ (σ⁻¹ α) = χ * (σ⁻¹ α) := by
      rw [hχdef, hcoc, div_mul_cancel₀ _ hβ0]
    calc (σ * τ * σ⁻¹) α = σ (τ (σ⁻¹ α)) := by simp only [AlgEquiv.mul_apply]
    _ = σ (χ * σ⁻¹ α) := by rw [key]
    _ = σ χ * σ (σ⁻¹ α) := by rw [map_mul]
    _ = χ ^ q * α := by
        rw [hσμ _ hχm, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  rw [hLHS, hRHS]

end WCOTTameR

end

section
open IntermediateField
open scoped Pointwise

namespace WCOTTameU

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem isClosed_apply_mem [Algebra.IsIntegral K L] (A : ValuationSubring L) (x : L) :
    IsClosed {σ : L ≃ₐ[K] L | σ x ∈ A} := by
  rw [← isOpen_compl_iff]
  have hcompl : {σ : L ≃ₐ[K] L | σ x ∈ A}ᶜ =
      ⋃ σ₀ ∈ {σ : L ≃ₐ[K] L | σ x ∉ A},
        σ₀ • (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) := by
    ext σ
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro h
      refine ⟨σ, h, ?_⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp
    · rintro ⟨σ₀, h₀, hmem⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hmem
      have hfix : (σ₀⁻¹ * σ) • x = x := hmem
      rw [mul_smul] at hfix
      have hx : σ • x = σ₀ • x := by
        have := congrArg (σ₀ • ·) hfix
        simpa [smul_smul] using this
      intro hA
      apply h₀
      have : σ₀ x = σ x := by simpa [AlgEquiv.smul_def] using hx.symm
      rwa [this]
  rw [hcompl]
  exact isOpen_biUnion fun σ₀ _ =>
    (stabilizer_isOpen_of_isIntegral (K := K) x).smul σ₀

theorem isClosed_decompositionSubgroup [Algebra.IsIntegral K L] (A : ValuationSubring L) :
    IsClosed ((A.decompositionSubgroup K : Subgroup (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L)) := by
  have hS : IsClosed {σ : L ≃ₐ[K] L | ∀ x ∈ A, σ x ∈ A} := by
    have hset : {σ : L ≃ₐ[K] L | ∀ x ∈ A, σ x ∈ A} =
        ⋂ x ∈ (A : Set L), {σ : L ≃ₐ[K] L | σ x ∈ A} := by
      ext σ; simp
    rw [hset]
    exact isClosed_biInter fun x _ => isClosed_apply_mem A x
  have hset : ((A.decompositionSubgroup K : Subgroup (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L)) =
      {σ : L ≃ₐ[K] L | ∀ x ∈ A, σ x ∈ A} ∩
        (fun σ : L ≃ₐ[K] L => σ⁻¹) ⁻¹' {σ : L ≃ₐ[K] L | ∀ x ∈ A, σ x ∈ A} := by
    ext σ
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro hσ
      have h : σ • A = A := hσ
      constructor
      · intro x hx
        have hmem : σ • x ∈ σ • A := ValuationSubring.smul_mem_pointwise_smul σ x A hx
        rw [h] at hmem
        simpa [AlgEquiv.smul_def] using hmem
      · intro x hx
        rw [← h] at hx
        have := ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem.mp hx
        simpa [AlgEquiv.smul_def] using this
    · rintro ⟨h₁, h₂⟩
      show σ • A = A
      ext y
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      constructor
      · intro hy
        have := h₁ _ hy
        simpa [AlgEquiv.smul_def, smul_inv_smul] using this
      · intro hy
        simpa [AlgEquiv.smul_def] using h₂ y hy
  rw [hset]
  exact hS.inter (hS.preimage continuous_inv)

theorem fixingSubgroup_fixedField_map_inertia_le [IsGalois K L] [Algebra.IsIntegral K L]
    (A : ValuationSubring L) :
    (IntermediateField.fixedField
        ((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype)).fixingSubgroup ≤
      A.decompositionSubgroup K := by
  have hle : (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype ≤
      A.decompositionSubgroup K := by
    rintro σ ⟨τ, _, rfl⟩
    exact τ.2
  have hff : IntermediateField.fixedField (A.decompositionSubgroup K) ≤
      IntermediateField.fixedField
        ((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype) :=
    IntermediateField.fixedField_le hle
  have hfix := IntermediateField.fixingSubgroup_antitone hff
  refine hfix.trans (le_of_eq ?_)
  exact InfiniteGalois.fixingSubgroup_fixedField
    ⟨A.decompositionSubgroup K, isClosed_decompositionSubgroup A⟩

theorem smul_eq_self_of_mem_fixingSubgroup [IsGalois K L] [Algebra.IsIntegral K L]
    (A : ValuationSubring L) (σ : L ≃ₐ[K] L)
    (hσ : σ ∈ (IntermediateField.fixedField
        ((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype)).fixingSubgroup) :
    σ • A = A :=
  fixingSubgroup_fixedField_map_inertia_le A hσ

end WCOTTameU

end

section
open IntermediateField
open scoped Pointwise

namespace WCOTTameUI

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem isOpen_setOf_apply [Algebra.IsIntegral K L] (Q : L → Prop) (x : L) :
    IsOpen {σ : L ≃ₐ[K] L | Q (σ x)} := by
  have h : {σ : L ≃ₐ[K] L | Q (σ x)} = ⋃ σ₀ ∈ {σ : L ≃ₐ[K] L | Q (σ x)},
      σ₀ • (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hσ
      refine ⟨σ, hσ, ?_⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp
    · rintro ⟨σ₀, h₀, hmem⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hmem
      have hfix : (σ₀⁻¹ * σ) • x = x := hmem
      rw [mul_smul] at hfix
      have hx : σ • x = σ₀ • x := by
        have := congrArg (σ₀ • ·) hfix
        simpa [smul_smul] using this
      have : σ x = σ₀ x := by simpa [AlgEquiv.smul_def] using hx
      rw [this]
      exact h₀
  rw [h]
  exact isOpen_biUnion fun σ₀ _ => (stabilizer_isOpen_of_isIntegral (K := K) x).smul σ₀

theorem isClosed_setOf_apply [Algebra.IsIntegral K L] (Q : L → Prop) (x : L) :
    IsClosed {σ : L ≃ₐ[K] L | Q (σ x)} := by
  rw [← isOpen_compl_iff]
  have : {σ : L ≃ₐ[K] L | Q (σ x)}ᶜ = {σ : L ≃ₐ[K] L | ¬ Q (σ x)} := by ext; simp
  rw [this]
  exact isOpen_setOf_apply (fun y => ¬ Q y) x

theorem mem_inertia_map_iff (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    σ ∈ (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype ↔
      σ ∈ A.decompositionSubgroup K ∧ ∀ a : A, A.valuation (σ a - a) < 1 := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨τ.2, fun a => ?_⟩
    change τ ∈ MonoidHom.ker (MulSemiringAction.toRingAut (A.decompositionSubgroup K)
      (IsLocalRing.ResidueField A)) at hτ
    rw [MonoidHom.mem_ker] at hτ
    have h1 : τ • IsLocalRing.residue A a = IsLocalRing.residue A a := RingEquiv.congr_fun hτ _
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff] at h1
    exact h1
  · rintro ⟨hD, hv⟩
    refine ⟨⟨σ, hD⟩, ?_, rfl⟩
    change (⟨σ, hD⟩ : A.decompositionSubgroup K) ∈ MonoidHom.ker (MulSemiringAction.toRingAut
      (A.decompositionSubgroup K) (IsLocalRing.ResidueField A))
    rw [MonoidHom.mem_ker]
    apply RingEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    change (⟨σ, hD⟩ : A.decompositionSubgroup K) • IsLocalRing.residue A a = IsLocalRing.residue A a
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    exact hv a

theorem isClosed_inertia_map [Algebra.IsIntegral K L] (A : ValuationSubring L) :
    IsClosed (((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype : Subgroup (L ≃ₐ[K] L)) :
      Set (L ≃ₐ[K] L)) := by
  have hset : (((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype : Subgroup (L ≃ₐ[K] L)) :
      Set (L ≃ₐ[K] L)) =
      ((A.decompositionSubgroup K : Subgroup (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L)) ∩
        ⋂ a : A, {σ : L ≃ₐ[K] L | A.valuation (σ a - a) < 1} := by
    ext σ
    rw [SetLike.mem_coe, mem_inertia_map_iff, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_iInter]
    rfl
  rw [hset]
  exact (WCOTTameU.isClosed_decompositionSubgroup A).inter
    (isClosed_iInter fun a => isClosed_setOf_apply (fun y => A.valuation (y - a) < 1) a)

theorem topologicalClosure_inertia_map [Algebra.IsIntegral K L] (A : ValuationSubring L) :
    ((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype).topologicalClosure =
      (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype :=
  le_antisymm (Subgroup.topologicalClosure_minimal _ le_rfl (isClosed_inertia_map A))
    (Subgroup.le_topologicalClosure _)

end WCOTTameUI

end

section
open IntermediateField
open scoped Pointwise

namespace WCOTTameJg

variable (k : Type) {L : Type} [Field k] [Field L] [Algebra k L]

noncomputable abbrev Iner (A : ValuationSubring L) : Subgroup (L ≃ₐ[k] L) :=
  (A.inertiaSubgroup k).map (A.decompositionSubgroup k).subtype

end WCOTTameJg

end

section
open IntermediateField
open scoped Pointwise

namespace WCOTTameGen

open WCOTTameJg

variable {k : Type} {L : Type} [Field k] [Field L] [Algebra k L]

noncomputable def kum (x : L ≃ₐ[k] L) (α : L) : L := x α * α⁻¹

theorem apply_eq_kum_mul (x : L ≃ₐ[k] L) {α : L} (hα : α ≠ 0) : x α = kum x α * α := by
  rw [kum, inv_mul_cancel_right₀ hα]

theorem kum_pow (x : L ≃ₐ[k] L) (α : L) (N : ℕ) : kum x α ^ N = kum x (α ^ N) := by
  rw [kum, kum, mul_pow, map_pow, inv_pow]

theorem kum_eq_one_iff (x : L ≃ₐ[k] L) {α : L} (hα : α ≠ 0) : kum x α = 1 ↔ x α = α := by
  rw [kum, mul_inv_eq_one₀ hα]

theorem kum_mul (x y : L ≃ₐ[k] L) {α : L} (hα : α ≠ 0) (hfix : x (kum y α) = kum y α) :
    kum (x * y) α = kum x α * kum y α := by
  have hy : y α = kum y α * α := apply_eq_kum_mul y hα
  change (x * y) α * α⁻¹ = (x α * α⁻¹) * kum y α
  rw [AlgEquiv.mul_apply, hy, map_mul, hfix]
  ring

theorem kum_pow_left (x : L ≃ₐ[k] L) {α : L} (hα : α ≠ 0)
    (hfix : ∀ j : ℕ, x (kum x α ^ j) = kum x α ^ j) : ∀ j : ℕ, kum (x ^ j) α = kum x α ^ j
  | 0 => by rw [pow_zero, pow_zero, kum, AlgEquiv.one_apply, mul_inv_cancel₀ hα]
  | j + 1 => by
    have ih := kum_pow_left x hα hfix j
    have h := kum_mul x (x ^ j) hα (by rw [ih]; exact hfix j)
    rw [pow_succ' x j, h, ih, ← pow_succ']

theorem exists_tame_generator [IsAlgClosed L] [CharZero L] [IsGalois k L]
    (A : ValuationSubring L) {p q : ℕ} (hp : p.Prime) (hq' : q.Prime)
    (hpq : p ≠ q) (hq : A.LiesOverPrime q) (m : ℕ)
    (htail : ∀ (h : L ≃ₐ[k] L), h ∈ A.inertiaSubgroupIn k →
      (∀ (s : L) (n : ℕ), s ^ (p ^ n) = (q : L) → h s = s) → ∃ w ∈ A.inertiaSubgroupIn k, w ^ (p ^ m) = h) :
    ∃ γ : L ≃ₐ[k] L, γ ∈ A.inertiaSubgroupIn k ∧ ∀ τ : L ≃ₐ[k] L, τ ∈ A.inertiaSubgroupIn k →
      ∃ (j : ℕ) (x w : L ≃ₐ[k] L), x ∈ A.inertiaSubgroupIn k ∧ w ∈ A.inertiaSubgroupIn k ∧
        τ = γ ^ j * x ^ (p ^ m) * w ^ (p ^ m) := by
  classical
  haveI := Fact.mk hp
  set I : Subgroup (L ≃ₐ[k] L) := Iner k A with hI
  change ∃ γ : L ≃ₐ[k] L, γ ∈ I ∧ ∀ τ : L ≃ₐ[k] L, τ ∈ I →
      ∃ (j : ℕ) (x w : L ≃ₐ[k] L), x ∈ I ∧ w ∈ I ∧ τ = γ ^ j * x ^ (p ^ m) * w ^ (p ^ m)
  have hq0 : (q : L) ≠ 0 := Nat.cast_ne_zero.mpr hq'.ne_zero
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq').mpr hpq

  have hfixμ : ∀ x ∈ I, ∀ (N : ℕ) (ζ : L), ζ ^ (p ^ N) = 1 → x ζ = ζ := fun x hx N ζ hζ =>
    WCOTTameR.inertia_fixes_root_of_unity A hq (pow_ne_zero N hp.ne_zero) (Nat.Coprime.pow_left N hcop) ζ hζ x hx

  obtain ⟨α, hα0q, hαs⟩ : ∃ α : ℕ → L, α 0 = q ∧ ∀ n, α (n + 1) ^ p = α n := by
    choose f hf using fun y : L => IsAlgClosed.exists_pow_nat_eq y hp.pos
    exact ⟨fun n => Nat.rec (q : L) (fun _ y => f y) n, rfl, fun n => hf _⟩
  have hαle : ∀ n d, α (n + d) ^ (p ^ d) = α n := by
    intro n d
    induction d with
    | zero => rw [pow_zero, pow_one, Nat.add_zero]
    | succ d ih =>
      rw [pow_succ' p d, pow_mul]
      change (α (n + d + 1) ^ p) ^ p ^ d = α n
      rw [hαs, ih]
  have hαn : ∀ n, α n ^ (p ^ n) = (q : L) := fun n => by
    have := hαle 0 n; rwa [Nat.zero_add, hα0q] at this
  have hα0 : ∀ n, α n ≠ 0 := fun n h0 =>
    hq0 (by rw [← hαn n, h0, zero_pow (pow_ne_zero n hp.ne_zero)])

  have hχroot : ∀ (n : ℕ) (x : L ≃ₐ[k] L), kum x (α n) ^ (p ^ n) = 1 := by
    intro n x
    rw [kum_pow, hαn, kum, map_natCast, mul_inv_cancel₀ hq0]
  have hχcompat : ∀ (n d : ℕ) (x : L ≃ₐ[k] L), kum x (α (n + d)) ^ (p ^ d) = kum x (α n) := by
    intro n d x; rw [kum_pow, hαle]
  have hχfix : ∀ x ∈ I, ∀ (n : ℕ) (y : L ≃ₐ[k] L) (j : ℕ), x (kum y (α n) ^ j) = kum y (α n) ^ j := by
    intro x hx n y j
    apply hfixμ x hx n
    rw [← pow_mul, mul_comm, pow_mul, hχroot, one_pow]
  have hχpow : ∀ x ∈ I, ∀ (n j : ℕ), kum (x ^ j) (α n) = kum x (α n) ^ j := by
    intro x hx n j
    exact kum_pow_left x (hα0 n) (hχfix x hx n x) j

  have hdiv : ∀ h ∈ I, (∀ n, h (α n) = α n) → ∃ w ∈ I, w ^ (p ^ m) = h := by
    intro h hh hfixα
    have hrad : ∀ (s : L) (n : ℕ), s ^ (p ^ n) = (q : L) → h s = s := by
      intro s n hs
      have hζ : (s * (α n)⁻¹) ^ (p ^ n) = 1 := by
        rw [mul_pow, inv_pow, hs, hαn, mul_inv_cancel₀ hq0]
      have hs' : s = s * (α n)⁻¹ * α n := by rw [inv_mul_cancel_right₀ (hα0 n)]
      rw [hs', map_mul, hfixμ h hh n _ hζ, hfixα n]
    exact htail h hh hrad

  by_cases hP : ∀ (n : ℕ), ∀ x ∈ I, x (α n) = α n
  · refine ⟨1, Subgroup.one_mem _, fun τ hτ => ?_⟩
    obtain ⟨w, hw, hwτ⟩ := hdiv τ hτ (fun n => hP n τ hτ)
    exact ⟨0, 1, w, Subgroup.one_mem _, hw, by rw [pow_zero, one_pow, one_mul, one_mul, hwτ]⟩

  have hex : ∃ n, ∃ x ∈ I, x (α n) ≠ α n := by
    by_contra hcon
    apply hP
    intro n x hx
    by_contra hne
    exact hcon ⟨n, x, hx, hne⟩
  obtain ⟨τ₀, hτ₀I, hτ₀ne⟩ : ∃ x ∈ I, x (α (Nat.find hex)) ≠ α (Nat.find hex) := Nat.find_spec hex
  have hmin : ∀ n < Nat.find hex, ∀ x ∈ I, x (α n) = α n := by
    intro n hn x hx
    by_contra hne
    exact Nat.find_min hex hn ⟨x, hx, hne⟩
  have hn₁0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hτ₀ne
    rw [h0, hα0q, map_natCast]
  obtain ⟨e, he⟩ : ∃ e, Nat.find hex = e + 1 := Nat.exists_eq_succ_of_ne_zero hn₁0
  rw [he] at hτ₀ne hmin
  have hfixe : ∀ x ∈ I, x (α e) = α e := fun x hx => hmin e (Nat.lt_succ_self e) x hx
  have hχe : ∀ x ∈ I, ∀ d : ℕ, kum x (α (e + d)) ^ (p ^ d) = 1 := by
    intro x hx d
    rw [hχcompat, kum_eq_one_iff x (hα0 e)]
    exact hfixe x hx

  have hprim : ∀ d : ℕ, IsPrimitiveRoot (kum τ₀ (α (e + 1 + d))) (p ^ (d + 1)) := by
    intro d
    induction d with
    | zero =>
      have hne1 : kum τ₀ (α (e + 1)) ≠ 1 := by
        rw [Ne, kum_eq_one_iff τ₀ (hα0 _)]; exact hτ₀ne
      have hp1 : kum τ₀ (α (e + 1)) ^ p = 1 := by
        have := hχe τ₀ hτ₀I 1; rwa [pow_one] at this
      have hord : orderOf (kum τ₀ (α (e + 1))) = p := orderOf_eq_prime hp1 hne1
      have := IsPrimitiveRoot.orderOf (kum τ₀ (α (e + 1)))
      rw [hord] at this
      simpa only [Nat.add_zero, Nat.zero_add, pow_one] using this
    | succ d ih =>
      have hc := hχcompat (e + 1 + d) 1 τ₀
      rw [pow_one] at hc

      have hfin : kum τ₀ (α (e + 1 + (d + 1))) ^ p ^ (d + 1 + 1) = 1 := by
        rw [pow_succ' p (d + 1), pow_mul]
        change (kum τ₀ (α (e + 1 + d + 1)) ^ p) ^ p ^ (d + 1) = 1
        rw [hc]
        exact ih.pow_eq_one
      have hnot : ¬ kum τ₀ (α (e + 1 + (d + 1))) ^ p ^ (d + 1) = 1 := by
        intro h1
        rw [pow_succ' p d, pow_mul] at h1
        change (kum τ₀ (α (e + 1 + d + 1)) ^ p) ^ p ^ d = 1 at h1
        rw [hc] at h1
        have hdvd := (ih.pow_eq_one_iff_dvd (p ^ d)).mp h1
        rw [Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hdvd
        omega
      have hord := orderOf_eq_prime_pow hnot hfin
      have := IsPrimitiveRoot.orderOf (kum τ₀ (α (e + 1 + (d + 1))))
      rwa [hord] at this

  refine ⟨τ₀, hτ₀I, fun τ hτ => ?_⟩
  have hζN := hprim m
  haveI : NeZero (p ^ (m + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hτroot : kum τ (α (e + 1 + m)) ^ (p ^ (m + 1)) = 1 := by
    have := hχe τ hτ (1 + m)
    rwa [← Nat.add_assoc, Nat.add_comm 1 m] at this
  obtain ⟨j, -, hj⟩ := hζN.eq_pow_of_pow_eq_one hτroot
  have hjτ : (τ₀ ^ j) (α (e + 1 + m)) = τ (α (e + 1 + m)) := by
    rw [apply_eq_kum_mul (τ₀ ^ j) (hα0 _), apply_eq_kum_mul τ (hα0 _), hχpow τ₀ hτ₀I _ j, hj]
  set g := (τ₀ ^ j)⁻¹ * τ with hg
  have hgI : g ∈ I := I.mul_mem (I.inv_mem (I.pow_mem hτ₀I j)) hτ
  have hgN : g (α (e + 1 + m)) = α (e + 1 + m) := by
    rw [hg, AlgEquiv.mul_apply, ← hjτ, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

  let C : ℕ → Set (L ≃ₐ[k] L) := fun d => (I : Set (L ≃ₐ[k] L)) ∩
      ((fun x : L ≃ₐ[k] L => x ^ (p ^ m)) ⁻¹'
        {y : L ≃ₐ[k] L | y (α (e + 1 + m + d)) = g (α (e + 1 + m + d))})
  have hCcl : ∀ d, IsClosed (C d) := fun d =>
    (WCOTTameUI.isClosed_inertia_map A).inter
      ((WCOTTameUI.isClosed_setOf_apply (fun z => z = g (α (e + 1 + m + d))) (α (e + 1 + m + d))).preimage
        (continuous_pow (p ^ m)))
  have hCanti : ∀ d, C (d + 1) ⊆ C d := by
    intro d x hx
    refine ⟨hx.1, ?_⟩
    have h2 : (x ^ p ^ m) (α (e + 1 + m + d + 1)) = g (α (e + 1 + m + d + 1)) := hx.2
    show (x ^ p ^ m) (α (e + 1 + m + d)) = g (α (e + 1 + m + d))
    rw [← hαs (e + 1 + m + d), map_pow, map_pow, h2]
  have hCne : ∀ d, (C d).Nonempty := by
    intro d
    have hζ := hprim (m + d)
    have hlev : e + 1 + (m + d) = e + 1 + m + d := by omega
    rw [hlev] at hζ
    haveI : NeZero (p ^ (m + d + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have hgroot : kum g (α (e + 1 + m + d)) ^ (p ^ (m + d + 1)) = 1 := by
      have := hχe g hgI (1 + m + d)
      rwa [show e + (1 + m + d) = e + 1 + m + d by omega, show 1 + m + d = m + d + 1 by omega] at this
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hgroot
    have hgd : kum g (α (e + 1 + m + d)) ^ (p ^ d) = 1 := by
      rw [hχcompat (e + 1 + m) d g, kum_eq_one_iff g (hα0 _)]; exact hgN
    have hdvd : p ^ (m + d + 1) ∣ i * p ^ d := by
      rw [← hζ.pow_eq_one_iff_dvd, pow_mul, hi, hgd]
    have hdvd' : p ^ m ∣ i := by
      have h1 : p ^ (m + 1) * p ^ d ∣ i * p ^ d := by
        rwa [← pow_add, show m + 1 + d = m + d + 1 by omega]
      have h2 : p ^ (m + 1) ∣ i := Nat.dvd_of_mul_dvd_mul_right (pow_pos hp.pos d) h1
      exact dvd_trans (pow_dvd_pow p (Nat.le_succ m)) h2
    obtain ⟨i', rfl⟩ := hdvd'
    refine ⟨τ₀ ^ i', I.pow_mem hτ₀I i', ?_⟩
    show ((τ₀ ^ i') ^ p ^ m) (α (e + 1 + m + d)) = g (α (e + 1 + m + d))
    rw [← pow_mul, apply_eq_kum_mul (τ₀ ^ (i' * p ^ m)) (hα0 _), apply_eq_kum_mul g (hα0 _),
      hχpow τ₀ hτ₀I, mul_comm i' (p ^ m), hi]
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hCanti hCne
    (hCcl 0).isCompact hCcl
  have hxI : x ∈ I := (Set.mem_iInter.mp hx 0).1
  have hxd : ∀ d, (x ^ p ^ m) (α (e + 1 + m + d)) = g (α (e + 1 + m + d)) := fun d => (Set.mem_iInter.mp hx d).2

  set h := (x ^ p ^ m)⁻¹ * g with hh
  have hhI : h ∈ I := I.mul_mem (I.inv_mem (I.pow_mem hxI _)) hgI
  have hhfix : ∀ n, h (α n) = α n := by
    intro n
    have h1 : h (α (e + 1 + m + n)) = α (e + 1 + m + n) := by
      rw [hh, AlgEquiv.mul_apply, ← hxd n, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    rw [← hαle n (e + 1 + m), Nat.add_comm n (e + 1 + m), map_pow, h1]
  obtain ⟨w, hwI, hw⟩ := hdiv h hhI hhfix
  refine ⟨j, x, w, hxI, hwI, ?_⟩
  rw [hw, hh, mul_assoc, mul_inv_cancel_left, hg, mul_inv_cancel_left]

end WCOTTameGen

end

set_option backward.isDefEq.respectTransparency false in

theorem solution
    {p q : ℕ} (hp : p.Prime) (hq' : q.Prime) (hpq : p ≠ q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hq : P.LiesOverPrime q) (m : ℕ) :
    ∃ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, γ ∈ P.inertiaSubgroupIn ℚ ∧
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∃ (j : ℕ) (x w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        x ∈ P.inertiaSubgroupIn ℚ ∧ w ∈ P.inertiaSubgroupIn ℚ ∧ τ = γ ^ j * x ^ (p ^ m) * w ^ (p ^ m) := by
  obtain ⟨γ, hγ, h⟩ := WCOTTameGen.exists_tame_generator (k := ℚ) P hp hq' hpq hq m
    (fun h hh hrad => ValuationSubring.exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq hp hq' hpq P hq m h hh hrad)
  exact ⟨γ, hγ, fun τ hτ => h τ hτ⟩

end S_ValuationSubring_exists_tame_generator_inertiaSubgroupIn
end P2MW
export P2MW.S_ValuationSubring_exists_tame_generator_inertiaSubgroupIn (solution)
