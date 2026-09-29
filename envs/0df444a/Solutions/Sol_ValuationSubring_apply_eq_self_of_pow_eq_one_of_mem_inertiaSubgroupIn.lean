-- Prove2me | solution 1 for ValuationSubring.apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d14c7e82-8862-5318-8091-ef06e83ef6e7

import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Int.GCD
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn

open scoped Pointwise

namespace MuInert

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

lemma mem_inertiaSubgroupIn_iff {A : ValuationSubring L} {σ : L ≃ₐ[K] L} :
    σ ∈ A.inertiaSubgroupIn K ↔
      ∃ h : σ ∈ A.decompositionSubgroup K,
        (⟨σ, h⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K := by
  constructor
  · rintro ⟨⟨τ, hτ⟩, hτI, rfl⟩
    exact ⟨hτ, hτI⟩
  · rintro ⟨h, hI⟩
    exact ⟨⟨σ, h⟩, hI, rfl⟩

theorem apply_mem_iff {A : ValuationSubring L} {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) (x : L) : σ x ∈ A ↔ x ∈ A := by
  have hσ' : σ⁻¹ • A = A :=
    MulAction.mem_stabilizer_iff.mp ((A.decompositionSubgroup K).inv_mem hσ)
  calc σ x ∈ A ↔ σ • x ∈ A := Iff.rfl
    _ ↔ x ∈ σ⁻¹ • A := by rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    _ ↔ x ∈ A := by rw [hσ']

theorem apply_sub_self_mem_nonunits {A : ValuationSubring L}
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.inertiaSubgroupIn K) {x : L} (hx : x ∈ A) :
    σ x - x ∈ A.nonunits := by
  obtain ⟨hd, hI⟩ := mem_inertiaSubgroupIn_iff.mp hσ
  set a : A := ⟨x, hx⟩
  set g : A.decompositionSubgroup K := ⟨σ, hd⟩
  have hker : MulSemiringAction.toRingAut (A.decompositionSubgroup K)
      (IsLocalRing.ResidueField A) g = 1 := MonoidHom.mem_ker.mp hI
  have happ : (MulSemiringAction.toRingAut (A.decompositionSubgroup K)
      (IsLocalRing.ResidueField A) g) (IsLocalRing.residue A a)
      = g • (IsLocalRing.residue A a) := rfl
  have hres : IsLocalRing.residue A (g • a) = IsLocalRing.residue A a := by
    rw [IsLocalRing.ResidueField.residue_smul, ← happ, hker]
    rfl
  have hmem : g • a - a ∈ IsLocalRing.maximalIdeal A := by
    have h0 : IsLocalRing.residue A (g • a - a) = 0 := by
      rw [map_sub, hres, sub_self]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  have hcoe : ((g • a - a : A) : L) = σ x - x := rfl
  have := (ValuationSubring.coe_mem_nonunits_iff (A := A)).mpr hmem
  rwa [hcoe] at this

theorem mul_mem_nonunits {A : ValuationSubring L} {a b : L} (ha : a ∈ A.nonunits) (hb : b ∈ A) :
    a * b ∈ A.nonunits := by
  have ha' : a ∈ A := A.nonunits_subset ha
  have h1 : (⟨a, ha'⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
    ValuationSubring.coe_mem_nonunits_iff.mp ha
  have h2 : (⟨a, ha'⟩ * ⟨b, hb⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
    Ideal.mul_mem_right _ _ h1
  exact ValuationSubring.coe_mem_nonunits_iff.mpr h2

theorem apply_eq_self_of_pow_eq_one {A : ValuationSubring L} {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.inertiaSubgroupIn K) {n : ℕ} (hn0 : n ≠ 0) (hnA : (n : L) ∉ A.nonunits)
    {ζ : L} (hζ : ζ ^ n = 1) : σ ζ = ζ := by
  have hσD : σ ∈ A.decompositionSubgroup K := (mem_inertiaSubgroupIn_iff.mp hσ).1
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn0] at hζ
    exact zero_ne_one hζ

  have hvζ : A.valuation ζ = 1 := by
    have h : A.valuation ζ ^ n = 1 := by rw [← map_pow, hζ, map_one]
    exact (pow_eq_one_iff_of_nonneg zero_le' hn0).mp h
  have hζA : ζ ∈ A := by rw [← ValuationSubring.valuation_le_one_iff, hvζ]
  have hζinvA : ζ⁻¹ ∈ A := by
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hvζ, inv_one]

  have hσζA : σ ζ ∈ A := (apply_mem_iff hσD ζ).mpr hζA
  have hηA : σ ζ * ζ⁻¹ ∈ A := A.mul_mem _ _ hσζA hζinvA
  have hηn : (σ ζ * ζ⁻¹) ^ n = 1 := by
    rw [mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ, inv_one, mul_one]
  have hη1 : σ ζ * ζ⁻¹ - 1 ∈ A.nonunits := by
    have e : σ ζ * ζ⁻¹ - 1 = (σ ζ - ζ) * ζ⁻¹ := by field_simp
    rw [e]
    exact mul_mem_nonunits (apply_sub_self_mem_nonunits hσ hζA) hζinvA

  set e : A := ⟨σ ζ * ζ⁻¹, hηA⟩ with he
  have hen : e ^ n = 1 := Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hηn)
  have hres1 : IsLocalRing.residue A e = 1 := by
    rw [← (IsLocalRing.residue A).map_one]
    apply Ideal.Quotient.eq.mpr
    exact ValuationSubring.coe_mem_nonunits_iff.mp hη1

  rcases mul_eq_zero.mp (show (∑ i ∈ Finset.range n, e ^ i) * (e - 1) = 0 by
      rw [geom_sum_mul, hen, sub_self]) with hsum | he1
  ·
    exfalso
    apply hnA
    have hresn : IsLocalRing.residue A (n : A) = 0 := by
      have := congrArg (IsLocalRing.residue A) hsum
      rw [map_sum, _root_.map_zero] at this
      simp only [map_pow, hres1, one_pow, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one] at this
      rw [map_natCast]
      exact this
    have hmem : (n : A) ∈ IsLocalRing.maximalIdeal A := Ideal.Quotient.eq_zero_iff_mem.mp hresn
    have := ValuationSubring.coe_mem_nonunits_iff.mpr hmem
    simpa using this
  ·
    have h1 : σ ζ * ζ⁻¹ = 1 := by
      have := congrArg (fun t : A => (t : L)) (sub_eq_zero.mp he1)
      simpa [he] using this
    calc σ ζ = σ ζ * ζ⁻¹ * ζ := by rw [mul_assoc, inv_mul_cancel₀ hζ0, mul_one]
      _ = ζ := by rw [h1, one_mul]

end MuInert

open MuInert in

theorem solution {q : ℕ} (hq : q.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) {n : ℕ} (hn : ¬ q ∣ n) {ζ : AlgebraicClosure ℚ} (hζ : ζ ^ n = 1) : σ ζ = ζ := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero q)
  refine apply_eq_self_of_pow_eq_one hσ hn0 ?_ hζ

  intro hnA
  have hcop : Nat.Coprime q n := (Nat.Prime.coprime_iff_not_dvd hq).mpr hn
  have hbez : ((q : ℤ) * Nat.gcdA q n + (n : ℤ) * Nat.gcdB q n : ℤ) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]; rfl
  have hone : (1 : AlgebraicClosure ℚ) ∈ A.nonunits := by
    have e : (1 : AlgebraicClosure ℚ) =
        (q : AlgebraicClosure ℚ) * (Nat.gcdA q n : ℤ) + (n : AlgebraicClosure ℚ) * (Nat.gcdB q n : ℤ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : AlgebraicClosure ℚ)) hbez.symm
    rw [e]
    exact add_mem (mul_mem_nonunits hA (intCast_mem A.toSubring _))
      (mul_mem_nonunits hnA (intCast_mem A.toSubring _))
  rw [ValuationSubring.mem_nonunits_iff, map_one] at hone
  exact lt_irrefl 1 hone

end S_ValuationSubring_apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn
end P2MW
export P2MW.S_ValuationSubring_apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn (solution)
