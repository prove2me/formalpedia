-- Prove2me | solution 1 for ValuationSubring.exists_forall_tame_generator_inertiaSubgroupIn_of_isGalois
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/fa443190-a210-506e-a8ce-846f6debd9c0

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq_of_isGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_forall_tame_generator_inertiaSubgroupIn_of_isGalois
p2m_attr_erase "instance" "GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq"

set_option autoImplicit false

section
open Finset IsLocalRing

namespace TGATameR

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
    first | exact hq | simpa using hq | simpa +zetaDelta using hq
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

end TGATameR

end

section
open IntermediateField
open scoped Pointwise

namespace TGATameU

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

end TGATameU

end

section
open IntermediateField
open scoped Pointwise

namespace TGATameUI

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
  exact (TGATameU.isClosed_decompositionSubgroup A).inter
    (isClosed_iInter fun a => isClosed_setOf_apply (fun y => A.valuation (y - a) < 1) a)

theorem topologicalClosure_inertia_map [Algebra.IsIntegral K L] (A : ValuationSubring L) :
    ((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype).topologicalClosure =
      (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype :=
  le_antisymm (Subgroup.topologicalClosure_minimal _ le_rfl (isClosed_inertia_map A))
    (Subgroup.le_topologicalClosure _)

end TGATameUI

end

section
open IntermediateField
open scoped Pointwise

namespace TGATameJg

variable (k : Type) {L : Type} [Field k] [Field L] [Algebra k L]

noncomputable abbrev Iner (A : ValuationSubring L) : Subgroup (L ≃ₐ[k] L) :=
  (A.inertiaSubgroup k).map (A.decompositionSubgroup k).subtype

end TGATameJg

section
open IntermediateField
open scoped Pointwise

namespace TGATameGen

open TGATameJg

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

section engine

variable [IsAlgClosed L] [CharZero L] [IsGalois k L]

def Tail (A : ValuationSubring L) (p q m : ℕ) : Prop :=
  ∀ (h : L ≃ₐ[k] L), h ∈ A.inertiaSubgroupIn k →
    (∀ (s : L) (n : ℕ), s ^ (p ^ n) = (q : L) → h s = s) → ∃ w ∈ A.inertiaSubgroupIn k, w ^ (p ^ m) = h

theorem forall_eq_pow_mul_of_mover
    (A : ValuationSubring L) {p q : ℕ} (hp : p.Prime) (hq' : q.Prime)
    (hpq : p ≠ q) (hq : A.LiesOverPrime q)
    (α : ℕ → L) (hα0q : α 0 = q) (hαs : ∀ n, α (n + 1) ^ p = α n)
    (e : ℕ) (hfixe : ∀ x ∈ Iner k A, x (α e) = α e)
    (τ₀ : L ≃ₐ[k] L) (hτ₀I : τ₀ ∈ Iner k A) (hτ₀ne : τ₀ (α (e + 1)) ≠ α (e + 1))
    (m : ℕ) (htail : Tail (k := k) A p q m) :
    ∀ τ : L ≃ₐ[k] L, τ ∈ Iner k A →
      ∃ (j : ℕ) (x w : L ≃ₐ[k] L), x ∈ Iner k A ∧ w ∈ Iner k A ∧
        τ = τ₀ ^ j * x ^ (p ^ m) * w ^ (p ^ m) := by
  classical
  haveI := Fact.mk hp
  set I : Subgroup (L ≃ₐ[k] L) := Iner k A with hI
  have htail' : ∀ (h : L ≃ₐ[k] L), h ∈ I →
      (∀ (s : L) (n : ℕ), s ^ (p ^ n) = (q : L) → h s = s) → ∃ w ∈ I, w ^ (p ^ m) = h := htail
  intro τ hτ
  have hq0 : (q : L) ≠ 0 := Nat.cast_ne_zero.mpr hq'.ne_zero
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq').mpr hpq

  have hfixμ : ∀ x ∈ I, ∀ (N : ℕ) (ζ : L), ζ ^ (p ^ N) = 1 → x ζ = ζ := fun x hx N ζ hζ =>
    TGATameR.inertia_fixes_root_of_unity A hq (pow_ne_zero N hp.ne_zero) (Nat.Coprime.pow_left N hcop) ζ hζ x hx
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
    exact htail' h hh hrad
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
    (TGATameUI.isClosed_inertia_map A).inter
      ((TGATameUI.isClosed_setOf_apply (fun z => z = g (α (e + 1 + m + d))) (α (e + 1 + m + d))).preimage
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

theorem forall_eq_pow_mul_of_forall_fix
    (A : ValuationSubring L) {p q : ℕ} (hp : p.Prime) (hq' : q.Prime)
    (hpq : p ≠ q) (hq : A.LiesOverPrime q)
    (α : ℕ → L) (hα0q : α 0 = q) (hαs : ∀ n, α (n + 1) ^ p = α n)
    (hP : ∀ (n : ℕ), ∀ x ∈ Iner k A, x (α n) = α n)
    (γ : L ≃ₐ[k] L) (m : ℕ) (htail : Tail (k := k) A p q m) :
    ∀ τ : L ≃ₐ[k] L, τ ∈ Iner k A →
      ∃ (j : ℕ) (x w : L ≃ₐ[k] L), x ∈ Iner k A ∧ w ∈ Iner k A ∧
        τ = γ ^ j * x ^ (p ^ m) * w ^ (p ^ m) := by
  classical
  haveI := Fact.mk hp
  set I : Subgroup (L ≃ₐ[k] L) := Iner k A with hI
  have htail' : ∀ (h : L ≃ₐ[k] L), h ∈ I →
      (∀ (s : L) (n : ℕ), s ^ (p ^ n) = (q : L) → h s = s) → ∃ w ∈ I, w ^ (p ^ m) = h := htail
  intro τ hτ
  have hq0 : (q : L) ≠ 0 := Nat.cast_ne_zero.mpr hq'.ne_zero
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq').mpr hpq
  have hfixμ : ∀ x ∈ I, ∀ (N : ℕ) (ζ : L), ζ ^ (p ^ N) = 1 → x ζ = ζ := fun x hx N ζ hζ =>
    TGATameR.inertia_fixes_root_of_unity A hq (pow_ne_zero N hp.ne_zero) (Nat.Coprime.pow_left N hcop) ζ hζ x hx
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
  have hrad : ∀ (s : L) (n : ℕ), s ^ (p ^ n) = (q : L) → τ s = s := by
    intro s n hs
    have hζ : (s * (α n)⁻¹) ^ (p ^ n) = 1 := by
      rw [mul_pow, inv_pow, hs, hαn, mul_inv_cancel₀ hq0]
    have hs' : s = s * (α n)⁻¹ * α n := by rw [inv_mul_cancel_right₀ (hα0 n)]
    rw [hs', map_mul, hfixμ τ hτ n _ hζ, hP n τ hτ]
  obtain ⟨w, hw, hwτ⟩ := htail' τ hτ hrad
  exact ⟨0, 1, w, Subgroup.one_mem _, hw, by rw [pow_zero, one_pow, one_mul, one_mul, hwτ]⟩

theorem exists_forall_apply_ne_finset
    (I : Subgroup (L ≃ₐ[k] L)) (S : Finset ℕ) (β : ℕ → L)
    (hprime : ∀ p ∈ S, p.Prime) (hβ0 : ∀ p ∈ S, β p ≠ 0)
    (hroot : ∀ p ∈ S, ∀ x ∈ I, kum x (β p) ^ p = 1)
    (hfixμ : ∀ p ∈ S, ∀ x ∈ I, ∀ ζ : L, ζ ^ p = 1 → x ζ = ζ)
    (hmov : ∀ p ∈ S, ∃ τ ∈ I, τ (β p) ≠ β p) :
    ∃ γ ∈ I, ∀ p ∈ S, γ (β p) ≠ β p := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, I.one_mem, fun p hp => absurd hp (Finset.notMem_empty p)⟩
  | insert p S hpS ih =>
    obtain ⟨γ, hγI, hγ⟩ := ih (fun r hr => hprime r (Finset.mem_insert_of_mem hr))
      (fun r hr => hβ0 r (Finset.mem_insert_of_mem hr)) (fun r hr => hroot r (Finset.mem_insert_of_mem hr))
      (fun r hr => hfixμ r (Finset.mem_insert_of_mem hr)) (fun r hr => hmov r (Finset.mem_insert_of_mem hr))
    have hpm : p ∈ insert p S := Finset.mem_insert_self p S
    by_cases hγp : γ (β p) ≠ β p
    · refine ⟨γ, hγI, fun r hr => ?_⟩
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact hγp
      · exact hγ r hr
    rw [not_ne_iff] at hγp
    obtain ⟨τ, hτI, hτ⟩ := hmov p hpm

    set N : ℕ := ∏ r ∈ S, r with hN
    have hNp : Nat.Coprime N p := by
      rw [hN]
      refine Nat.Coprime.prod_left fun r hr => (Nat.coprime_primes (hprime r (Finset.mem_insert_of_mem hr)) (hprime p hpm)).mpr ?_
      rintro rfl; exact hpS hr
    have hp := hprime p hpm
    haveI := Fact.mk hp

    have hχτ : kum τ (β p) ≠ 1 := by rw [Ne, kum_eq_one_iff τ (hβ0 p hpm)]; exact hτ
    have hprimτ : IsPrimitiveRoot (kum τ (β p)) p := by
      have hord : orderOf (kum τ (β p)) = p := orderOf_eq_prime (hroot p hpm τ hτI) hχτ
      have := IsPrimitiveRoot.orderOf (kum τ (β p)); rwa [hord] at this

    have hχfix : ∀ r ∈ insert p S, ∀ x ∈ I, ∀ (j : ℕ), x (kum τ (β r) ^ j) = kum τ (β r) ^ j := by
      intro r hr x hx j
      apply hfixμ r hr x hx
      rw [← pow_mul, mul_comm, pow_mul, hroot r hr τ hτI, one_pow]
    have hχpow : ∀ r ∈ insert p S, ∀ (j : ℕ), kum (τ ^ j) (β r) = kum τ (β r) ^ j := by
      intro r hr j
      exact kum_pow_left τ (hβ0 r hr) (hχfix r hr τ hτI) j
    refine ⟨γ * τ ^ N, I.mul_mem hγI (I.pow_mem hτI N), fun r hr => ?_⟩
    rcases Finset.mem_insert.mp hr with rfl | hr
    ·
      have hne : kum τ (β r) ^ N ≠ 1 := by
        intro h1
        have hdvd := (hprimτ.pow_eq_one_iff_dvd N).mp h1
        exact (Nat.Prime.coprime_iff_not_dvd hp).mp hNp.symm hdvd
      intro heq
      apply hne
      have h1 : (γ * τ ^ N) (β r) = kum τ (β r) ^ N * β r := by
        rw [AlgEquiv.mul_apply, apply_eq_kum_mul (τ ^ N) (hβ0 r hpm), hχpow r hpm, map_mul, hγp,
          hχfix r hpm γ hγI]
      rw [h1] at heq
      exact (mul_eq_right₀ (hβ0 r hpm)).mp heq
    ·
      have hrN : r ∣ N := by rw [hN]; exact Finset.dvd_prod_of_mem _ hr
      have hfixN : (τ ^ N) (β r) = β r := by
        have hr' : r ∈ insert p S := Finset.mem_insert_of_mem hr
        rw [apply_eq_kum_mul (τ ^ N) (hβ0 r hr'), hχpow r hr']
        obtain ⟨c, hc⟩ := hrN
        rw [hc, pow_mul, hroot r hr' τ hτI, one_pow, one_mul]
      rw [AlgEquiv.mul_apply, hfixN]
      exact hγ r hr

theorem exists_forall_apply_ne
    (A : ValuationSubring L) (M : Set ℕ) (β : ℕ → L)
    (hprime : ∀ p ∈ M, p.Prime) (hβ0 : ∀ p ∈ M, β p ≠ 0)
    (hroot : ∀ p ∈ M, ∀ x ∈ Iner k A, kum x (β p) ^ p = 1)
    (hfixμ : ∀ p ∈ M, ∀ x ∈ Iner k A, ∀ ζ : L, ζ ^ p = 1 → x ζ = ζ)
    (hmov : ∀ p ∈ M, ∃ τ ∈ Iner k A, τ (β p) ≠ β p) :
    ∃ γ ∈ Iner k A, ∀ p ∈ M, γ (β p) ≠ β p := by
  classical
  set I : Subgroup (L ≃ₐ[k] L) := Iner k A with hI
  let C : ℕ → Set (L ≃ₐ[k] L) := fun d => (I : Set (L ≃ₐ[k] L)) ∩
      ⋂ (p : ℕ) (_ : p ∈ M ∧ p < d), {x : L ≃ₐ[k] L | x (β p) ≠ β p}
  have hCcl : ∀ d, IsClosed (C d) := fun d =>
    (TGATameUI.isClosed_inertia_map A).inter
      (isClosed_iInter fun p => isClosed_iInter fun _ =>
        TGATameUI.isClosed_setOf_apply (fun z => z ≠ β p) (β p))
  have hCanti : ∀ d, C (d + 1) ⊆ C d := by
    intro d x hx
    refine ⟨hx.1, Set.mem_iInter₂.mpr fun p hp => ?_⟩
    exact Set.mem_iInter₂.mp hx.2 p ⟨hp.1, Nat.lt_succ_of_lt hp.2⟩
  have hCne : ∀ d, (C d).Nonempty := by
    intro d
    let S : Finset ℕ := (Finset.range d).filter (· ∈ M)
    have hS : ∀ p ∈ S, p ∈ M := fun p hp => (Finset.mem_filter.mp hp).2
    obtain ⟨γ, hγI, hγ⟩ := exists_forall_apply_ne_finset I S β (fun p hp => hprime p (hS p hp))
      (fun p hp => hβ0 p (hS p hp)) (fun p hp => hroot p (hS p hp)) (fun p hp => hfixμ p (hS p hp))
      (fun p hp => hmov p (hS p hp))
    refine ⟨γ, hγI, Set.mem_iInter₂.mpr fun p hp => ?_⟩
    exact hγ p (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp.2, hp.1⟩)
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hCanti hCne
    (hCcl 0).isCompact hCcl
  refine ⟨x, (Set.mem_iInter.mp hx 0).1, fun p hp => ?_⟩
  exact Set.mem_iInter₂.mp (Set.mem_iInter.mp hx (p + 1)).2 p ⟨hp, Nat.lt_succ_self p⟩

theorem exists_forall_tame_generator
    (A : ValuationSubring L) {q : ℕ} (hq' : q.Prime) (hq : A.LiesOverPrime q)
    (htail : ∀ (p : ℕ), p.Prime → p ≠ q → ∀ (m : ℕ), Tail (k := k) A p q m) :
    ∃ γ : L ≃ₐ[k] L, γ ∈ A.inertiaSubgroupIn k ∧
      ∀ (p : ℕ), p.Prime → p ≠ q → ∀ (m : ℕ),
        ∀ τ : L ≃ₐ[k] L, τ ∈ A.inertiaSubgroupIn k →
          ∃ (j : ℕ) (x w : L ≃ₐ[k] L), x ∈ A.inertiaSubgroupIn k ∧ w ∈ A.inertiaSubgroupIn k ∧
            τ = γ ^ j * x ^ (p ^ m) * w ^ (p ^ m) := by
  classical
  set I : Subgroup (L ≃ₐ[k] L) := Iner k A with hI
  change ∃ γ : L ≃ₐ[k] L, γ ∈ I ∧ ∀ (p : ℕ), p.Prime → p ≠ q → ∀ (m : ℕ), ∀ τ : L ≃ₐ[k] L, τ ∈ I →
      ∃ (j : ℕ) (x w : L ≃ₐ[k] L), x ∈ I ∧ w ∈ I ∧ τ = γ ^ j * x ^ (p ^ m) * w ^ (p ^ m)
  have hq0 : (q : L) ≠ 0 := Nat.cast_ne_zero.mpr hq'.ne_zero

  choose f hf using fun (n : ℕ) (y : L) => IsAlgClosed.exists_pow_nat_eq y (Nat.succ_pos n)
  let α : ℕ → ℕ → L := fun p n => Nat.rec (q : L) (fun _ y => f (p - 1) y) n
  have hα0q : ∀ p, α p 0 = q := fun p => rfl
  have hαs : ∀ p, p.Prime → ∀ n, α p (n + 1) ^ p = α p n := by
    intro p hp n
    have h := hf (p - 1) (α p n)
    rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hp.one_le] at h
    exact h
  have hαle : ∀ p, p.Prime → ∀ n d, α p (n + d) ^ (p ^ d) = α p n := by
    intro p hp n d
    induction d with
    | zero => rw [pow_zero, pow_one, Nat.add_zero]
    | succ d ih =>
      rw [pow_succ' p d, pow_mul]
      change (α p (n + d + 1) ^ p) ^ p ^ d = α p n
      rw [hαs p hp, ih]
  have hαn : ∀ p, p.Prime → ∀ n, α p n ^ (p ^ n) = (q : L) := fun p hp n => by
    have := hαle p hp 0 n; rwa [Nat.zero_add] at this
  have hα0 : ∀ p, p.Prime → ∀ n, α p n ≠ 0 := fun p hp n h0 =>
    hq0 (by rw [← hαn p hp n, h0, zero_pow (pow_ne_zero n hp.ne_zero)])

  let Mov : ℕ → Prop := fun p => ∃ n, ∃ x ∈ I, x (α p n) ≠ α p n
  let dI : ∀ p, DecidablePred (fun n => ∃ x ∈ I, x (α p n) ≠ α p n) := fun p => Classical.decPred _
  let crit : ℕ → ℕ := fun p => @dite ℕ (Mov p) (Classical.dec (Mov p)) (fun h => @Nat.find _ (dI p) h) (fun _ => 0)
  let M : Set ℕ := {p | p.Prime ∧ p ≠ q ∧ Mov p}
  have hcrit : ∀ p (h : Mov p), crit p = @Nat.find _ (dI p) h := fun p h => dif_pos h
  have hcrit0 : ∀ p ∈ M, crit p ≠ 0 := by
    rintro p ⟨hp, -, h⟩ h0
    rw [hcrit p h] at h0
    obtain ⟨x, -, hx⟩ := @Nat.find_spec _ (dI p) h
    apply hx
    rw [h0]
    show x (q : L) = q
    exact map_natCast x q

  let β : ℕ → L := fun p => α p (crit p)
  have hfixbelow : ∀ p ∈ M, ∀ n < crit p, ∀ x ∈ I, x (α p n) = α p n := by
    rintro p ⟨hp, -, h⟩ n hn x hx
    rw [hcrit p h] at hn
    exact Classical.by_contradiction fun hne => @Nat.find_min _ (dI p) h n hn ⟨x, hx, hne⟩
  have hmov : ∀ p ∈ M, ∃ τ ∈ I, τ (β p) ≠ β p := by
    rintro p ⟨hp, hpq, h⟩
    obtain ⟨x, hx, hne⟩ := @Nat.find_spec _ (dI p) h
    refine ⟨x, hx, ?_⟩
    show x (α p (crit p)) ≠ α p (crit p)
    rw [hcrit p h]
    exact hne
  have hfixμ : ∀ p ∈ M, ∀ x ∈ I, ∀ ζ : L, ζ ^ p = 1 → x ζ = ζ := by
    rintro p ⟨hp, hpq, -⟩ x hx ζ hζ
    exact TGATameR.inertia_fixes_root_of_unity A hq hp.ne_zero ((Nat.coprime_primes hp hq').mpr hpq) ζ hζ x hx
  have hroot : ∀ p ∈ M, ∀ x ∈ I, kum x (β p) ^ p = 1 := by
    intro p hpM x hx
    obtain ⟨hp, hpq, h⟩ := hpM
    obtain ⟨e, he⟩ : ∃ e, crit p = e + 1 := Nat.exists_eq_succ_of_ne_zero (hcrit0 p ⟨hp, hpq, h⟩)
    have hfixe : x (α p e) = α p e := hfixbelow p ⟨hp, hpq, h⟩ e (by rw [he]; exact Nat.lt_succ_self e) x hx
    show kum x (α p (crit p)) ^ p = 1
    rw [he, kum_pow, hαs p hp, kum_eq_one_iff x (hα0 p hp e)]
    exact hfixe
  obtain ⟨γ, hγI, hγ⟩ := exists_forall_apply_ne (k := k) A M β (fun p hp => hp.1)
    (fun p hp => hα0 p hp.1 _) hroot hfixμ hmov
  refine ⟨γ, hγI, fun p hp hpq m τ hτ => ?_⟩
  rcases Classical.em (Mov p) with hM | hM
  ·
    have hpM : p ∈ M := ⟨hp, hpq, hM⟩
    obtain ⟨e, he⟩ : ∃ e, crit p = e + 1 := Nat.exists_eq_succ_of_ne_zero (hcrit0 p hpM)
    have hfixe : ∀ x ∈ I, x (α p e) = α p e := fun x hx =>
      hfixbelow p hpM e (by rw [he]; exact Nat.lt_succ_self e) x hx
    have hγne : γ (α p (e + 1)) ≠ α p (e + 1) := by
      have h1 : γ (α p (crit p)) ≠ α p (crit p) := hγ p hpM
      rwa [he] at h1
    exact forall_eq_pow_mul_of_mover (k := k) A hp hq' hpq hq (α p) (hα0q p) (hαs p hp) e hfixe γ hγI hγne m
      (htail p hp hpq m) τ hτ
  ·
    have hP : ∀ (n : ℕ), ∀ x ∈ I, x (α p n) = α p n := fun n x hx =>
      Classical.by_contradiction fun hne => hM ⟨n, x, hx, hne⟩
    exact forall_eq_pow_mul_of_forall_fix (k := k) A hp hq' hpq hq (α p) (hα0q p) (hαs p hp) hP γ m
      (htail p hp hpq m) τ hτ

end engine

end TGATameGen

end

theorem solution
    {k L : Type} [Field k] [Field L] [Algebra k L] [IsAlgClosed L] [CharZero L] [IsGalois k L]
    (halg : ∀ x : L, IsAlgebraic ℚ x)
    {q : ℕ} (hq' : q.Prime) (P : ValuationSubring L) (hq : P.LiesOverPrime q) :
    ∃ γ : L ≃ₐ[k] L, γ ∈ P.inertiaSubgroupIn k ∧
      ∀ (p : ℕ), p.Prime → p ≠ q → ∀ (m : ℕ),
        ∀ τ ∈ P.inertiaSubgroupIn k, ∃ (j : ℕ) (x w : L ≃ₐ[k] L),
          x ∈ P.inertiaSubgroupIn k ∧ w ∈ P.inertiaSubgroupIn k ∧ τ = γ ^ j * x ^ (p ^ m) * w ^ (p ^ m) := by
  obtain ⟨γ, hγ, h⟩ := TGATameGen.exists_forall_tame_generator (k := k) P hq' hq
    (fun p hp hpq m g hg hrad =>
      ValuationSubring.exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq_of_isGalois halg hp hq' hpq P hq m g hg hrad)
  exact ⟨γ, hγ, fun p hp hpq m τ hτ => h p hp hpq m τ hτ⟩

end
end S_ValuationSubring_exists_forall_tame_generator_inertiaSubgroupIn_of_isGalois
end P2MW
export P2MW.S_ValuationSubring_exists_forall_tame_generator_inertiaSubgroupIn_of_isGalois (solution)
