-- Prove2me | solution 1 for ValuationSubring.exists_mem_inertiaSubgroupIn_pow_eq_frobConj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8328cde5-eefa-5f7e-a887-82b21e598e98

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
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_frobConj

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

namespace WCOTTameJg

variable (k : Type) {L : Type} [Field k] [Field L] [Algebra k L]

noncomputable abbrev Iner (A : ValuationSubring L) : Subgroup (L ≃ₐ[k] L) :=
  (A.inertiaSubgroup k).map (A.decompositionSubgroup k).subtype

noncomputable def K0 (A : ValuationSubring L) : IntermediateField k L := fixedField (Iner k A)

def Rad (p q : ℕ) : Set L := {α : L | ∃ n : ℕ, α ^ (p ^ n) = (q : L)}

noncomputable def Kinf (A : ValuationSubring L) (p q : ℕ) : IntermediateField k L :=
  IntermediateField.adjoin k ((K0 k A : Set L) ∪ Rad p q)

variable {k}

theorem K0_le_Kinf (A : ValuationSubring L) (p q : ℕ) : K0 k A ≤ Kinf k A p q :=
  fun _ hx => IntermediateField.subset_adjoin k _ (Or.inl hx)

theorem mem_Kinf_of_pow_eq (A : ValuationSubring L) {p q : ℕ} {α : L} {n : ℕ} (h : α ^ (p ^ n) = (q : L)) :
    α ∈ Kinf k A p q :=
  IntermediateField.subset_adjoin k _ (Or.inr ⟨n, h⟩)

theorem frobConj_mem_Iner (A : ValuationSubring L) {q : ℕ} (σ τ : L ≃ₐ[k] L)
    (hσ : σ ∈ A.decompositionSubgroup k) (hτ : τ ∈ Iner k A) :
    σ * τ * σ⁻¹ * (τ ^ q)⁻¹ ∈ Iner k A := by
  refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hτ q))
  obtain ⟨τ', hτ', hττ⟩ := hτ
  have hN : (A.inertiaSubgroup k).Normal := by
    delta ValuationSubring.inertiaSubgroup
    exact MonoidHom.normal_ker _
  let s : A.decompositionSubgroup k := ⟨σ, hσ⟩
  have hmem : s * τ' * s⁻¹ ∈ A.inertiaSubgroup k := hN.conj_mem τ' hτ' s
  have heq : (A.decompositionSubgroup k).subtype (s * τ' * s⁻¹) = σ * τ * σ⁻¹ := by
    rw [map_mul, map_mul, map_inv, hττ]; rfl
  rw [Subgroup.mem_map]
  exact ⟨s * τ' * s⁻¹, hmem, heq⟩

theorem apply_eq_of_mem_adjoin (S : Set L) (g : L ≃ₐ[k] L) (hS : ∀ s ∈ S, g s = s) (x : L)
    (hx : x ∈ IntermediateField.adjoin k S) : g x = x := by
  have hle : IntermediateField.adjoin k S ≤ fixedField (Subgroup.zpowers g) := by
    rw [IntermediateField.adjoin_le_iff]
    intro s hs
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro h hh
    have hst : Subgroup.zpowers g ≤ MulAction.stabilizer (L ≃ₐ[k] L) s := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
      exact hS s hs
    exact hst hh
  have := (IntermediateField.mem_fixedField_iff _ _).mp (hle hx) g (Subgroup.mem_zpowers g)
  exact this

theorem frobConj_mem_fixingSubgroup_Kinf [CharZero L] (A : ValuationSubring L) {p q : ℕ} (hp : p.Prime)
    (hq : A.LiesOverPrime q) (hpq : p ≠ q) (hq' : q.Prime) (σ : L ≃ₐ[k] L) (hσ : A.IsFrobeniusAt σ q)
    (τ : L ≃ₐ[k] L) (hτ : τ ∈ Iner k A) :
    σ * τ * σ⁻¹ * (τ ^ q)⁻¹ ∈ (Kinf k A p q).fixingSubgroup := by
  set g := σ * τ * σ⁻¹ * (τ ^ q)⁻¹ with hg
  have hgI : g ∈ Iner k A := frobConj_mem_Iner A σ τ hσ.mem_decompositionSubgroup hτ
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  refine apply_eq_of_mem_adjoin _ g ?_ x hx
  rintro s (hs | ⟨n, hs⟩)
  · exact (IntermediateField.mem_fixedField_iff _ _).mp hs g hgI
  ·
    have hq0 : (q : L) ≠ 0 := Nat.cast_ne_zero.mpr hq'.ne_zero
    set β := (τ ^ q)⁻¹ s with hβ
    have hβn : β ^ (p ^ n) = (q : L) := by rw [hβ, ← map_pow, hs, map_natCast]
    have hβ0 : β ≠ 0 := by
      intro h0; rw [h0, zero_pow (pow_ne_zero _ hp.ne_zero)] at hβn; exact hq0 hβn.symm
    have hcop : Nat.Coprime (p ^ n) q := Nat.Coprime.pow_left n ((Nat.coprime_primes hp hq').mpr hpq)
    have hK := WCOTTameR.frob_conj_eq_pow_on_radical A hq (pow_ne_zero n hp.ne_zero) hcop τ hτ σ hσ β hβn hβ0

    rw [hg, AlgEquiv.mul_apply, ← hβ, hK, hβ, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

end WCOTTameJg

end

theorem solution
    {p q : ℕ} (hp : p.Prime) (hq' : q.Prime) (hpq : p ≠ q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hq : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : P.IsFrobeniusAt σ q) (n : ℕ) :
    ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∃ w ∈ P.inertiaSubgroupIn ℚ, w ^ (p ^ n) = σ * τ * σ⁻¹ * (τ ^ q)⁻¹ := by
  intro τ hτ
  have hτ' : τ ∈ WCOTTameJg.Iner ℚ P := hτ
  have hgE := WCOTTameJg.frobConj_mem_fixingSubgroup_Kinf (k := ℚ) P hp hq hpq hq' σ hσ τ hτ'
  have hgI : σ * τ * σ⁻¹ * (τ ^ q)⁻¹ ∈ P.inertiaSubgroupIn ℚ :=
    WCOTTameJg.frobConj_mem_Iner (k := ℚ) P σ τ hσ.mem_decompositionSubgroup hτ'
  obtain ⟨w, hw, hwe⟩ := ValuationSubring.exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq hp hq' hpq P hq n
    _ hgI (fun α k hα => (IntermediateField.mem_fixingSubgroup_iff _ _).mp hgE α (WCOTTameJg.mem_Kinf_of_pow_eq (k := ℚ) P hα))
  exact ⟨w, hw, hwe⟩

end S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_frobConj
end P2MW
export P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_frobConj (solution)
