-- Prove2me | solution 1 for ValuationSubring.IsFrobeniusAt.apply_rootOfUnity_eq_pow_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/e7160457-6f19-53e5-932d-6bd2aaf54aaf

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_IsFrobeniusAt_apply_rootOfUnity_eq_pow_of_not_dvd
set_option Elab.async false

set_option autoImplicit false

open IsLocalRing

namespace DeskDd6

section Place

variable {L : Type*} [Field L] {A : ValuationSubring L}

theorem vs_mul_mem_nonunits {a x : L} (ha : a ∈ A) (hx : x ∈ A.nonunits) :
    a * x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
  calc A.valuation (a * x) = A.valuation a * A.valuation x := map_mul _ _ _
    _ ≤ 1 * A.valuation x := mul_le_mul_left ((A.valuation_le_one_iff a).mpr ha) _
    _ = A.valuation x := one_mul _
    _ < 1 := hx

theorem vs_one_notMem_nonunits : (1 : L) ∉ A.nonunits := by
  simp [ValuationSubring.mem_nonunits_iff]

theorem vs_pow_mem_nonunits {x : L} (hx : x ∈ A.nonunits) {n : ℕ} (hn : n ≠ 0) :
    x ^ n ∈ A.nonunits := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ]
  exact vs_mul_mem_nonunits (pow_mem (A.nonunits_subset hx) m) hx

theorem vs_mem_of_pow_eq_one {ζ : L} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) : ζ ∈ A := by
  by_contra hmem
  have h2 : (ζ⁻¹) ^ n ∈ A.nonunits :=
    vs_pow_mem_nonunits (A.inv_mem_nonunits_iff.mpr (Or.inr hmem)) hn
  rw [inv_pow, hζ, inv_one] at h2
  exact vs_one_notMem_nonunits h2

theorem vs_notMem_nonunits_of_pow_eq_one {ζ : L} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) :
    ζ ∉ A.nonunits := fun h1 => vs_one_notMem_nonunits (A := A) (hζ ▸ vs_pow_mem_nonunits h1 hn)

theorem vs_eq_one_of_pow_eq_one_of_sub_one_mem_nonunits {m : ℕ}
    (hm : (m : ResidueField A) ≠ 0) {ω : L} (hω : ω ^ m = 1) (h1 : ω - 1 ∈ A.nonunits) :
    ω = 1 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  by_contra hne
  have hωA : ω ∈ A := vs_mem_of_pow_eq_one hm0 hω
  have hres : residue A (⟨ω, hωA⟩ : A) = 1 := by
    have hmem : (⟨ω, hωA⟩ : A) - 1 ∈ IsLocalRing.maximalIdeal A := by
      rw [← A.coe_mem_nonunits_iff]
      simpa using h1
    have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rwa [map_sub, map_one, sub_eq_zero] at h0
  have hgeom : (∑ i ∈ Finset.range m, (⟨ω, hωA⟩ : A) ^ i) = 0 := by
    have hL : (∑ i ∈ Finset.range m, ω ^ i) * (ω - 1) = 0 := by
      rw [geom_sum_mul, hω, sub_self]
    have hsum : (∑ i ∈ Finset.range m, ω ^ i) = 0 :=
      (mul_eq_zero.mp hL).resolve_right (sub_ne_zero.mpr hne)
    exact Subtype.ext (by push_cast; exact hsum)
  refine hm ?_
  have h0 := congrArg (residue A) hgeom
  rw [map_sum, map_zero] at h0
  simp only [map_pow, hres, one_pow] at h0
  simpa using h0

theorem vs_natCast_mem_maximalIdeal_of_liesOverPrime {q : ℕ} (h : A.LiesOverPrime q) :
    (q : A) ∈ IsLocalRing.maximalIdeal A := by
  have : ((q : A) : L) ∈ A.nonunits := by simp at h ⊢; exact h
  exact A.coe_mem_nonunits_iff.mp this

theorem vs_charP_residueField_of_liesOverPrime {q : ℕ} (hq : q.Prime)
    (h : A.LiesOverPrime q) : CharP (IsLocalRing.ResidueField A) q := by
  rw [CharP.charP_iff_prime_eq_zero hq]
  have : ((q : ℕ) : IsLocalRing.ResidueField A) = IsLocalRing.residue A ((q : ℕ) : A) := by
    simp
  rw [this]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (vs_natCast_mem_maximalIdeal_of_liesOverPrime h)

theorem vs_natCast_residueField_ne_zero_of_not_dvd {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) {m : ℕ} (hqm : ¬q ∣ m) : (m : ResidueField A) ≠ 0 := by
  haveI : CharP (ResidueField A) q := vs_charP_residueField_of_liesOverPrime hq hA
  rw [Ne, CharP.cast_eq_zero_iff (ResidueField A) q]
  exact hqm

variable {K : Type*} [Field K] [Algebra K L]

open scoped Pointwise in
theorem vs_smul_mem_of_mem_decompositionSubgroup {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) {z : L} (hz : z ∈ A) : σ z ∈ A := by
  have h1 : σ • z ∈ σ • A := ValuationSubring.smul_mem_pointwise_smul σ z A hz
  rwa [MulAction.mem_stabilizer_iff.mp hσ, AlgEquiv.smul_def] at h1

theorem frob_residue_smul_eq {σ : L ≃ₐ[K] L} {q : ℕ} (h : A.IsFrobeniusAt σ q) (a : A) :
    residue A ((⟨σ, h.mem_decompositionSubgroup⟩ : A.decompositionSubgroup K) • a) =
      (residue A a) ^ q := by
  rw [ResidueField.residue_smul]
  exact h.smul_residue_eq (residue A a)

theorem frob_apply_eq_pow_of_pow_eq_one {σ : L ≃ₐ[K] L} {q : ℕ}
    (h : A.IsFrobeniusAt σ q) {m : ℕ} (hm : (m : ResidueField A) ≠ 0) {ζ : L}
    (hζ : ζ ^ m = 1) : σ ζ = ζ ^ q := by
  have hσd := h.mem_decompositionSubgroup
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0] at hζ
    exact zero_ne_one hζ
  have hζA : ζ ∈ A := vs_mem_of_pow_eq_one hm0 hζ
  have hζnu : ζ ∉ A.nonunits := vs_notMem_nonunits_of_pow_eq_one hm0 hζ
  have hζinv : ζ⁻¹ ∈ A := by
    have h' := hζnu
    rw [ValuationSubring.mem_nonunits_iff_or] at h'
    exact not_not.mp (not_or.mp h').2
  have hσζA : σ ζ ∈ A := vs_smul_mem_of_mem_decompositionSubgroup hσd hζA
  have hres : residue A (⟨σ ζ, hσζA⟩ : A) = (residue A (⟨ζ, hζA⟩ : A)) ^ q := by
    have h1 : residue A (⟨σ ζ, hσζA⟩ : A)
        = residue A ((⟨σ, hσd⟩ : A.decompositionSubgroup K) • (⟨ζ, hζA⟩ : A)) := rfl
    rw [h1, frob_residue_smul_eq h]
  have hsub : σ ζ - ζ ^ q ∈ A.nonunits := by
    have h0 : residue A ((⟨σ ζ, hσζA⟩ : A) - (⟨ζ, hζA⟩ : A) ^ q) = 0 := by
      rw [map_sub, map_pow, hres, sub_self]
    have hmem : (⟨σ ζ, hσζA⟩ : A) - (⟨ζ, hζA⟩ : A) ^ q ∈ IsLocalRing.maximalIdeal A :=
      Ideal.Quotient.eq_zero_iff_mem.mp h0
    simpa using A.coe_mem_nonunits_iff.mpr hmem
  have hωm : (σ ζ * (ζ⁻¹) ^ q) ^ m = 1 := by
    have h1 : (σ ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
    have h2 : ((ζ⁻¹) ^ q) ^ m = 1 := by
      rw [← pow_mul, mul_comm q m, pow_mul, inv_pow, hζ, inv_one, one_pow]
    rw [mul_pow, h1, h2, one_mul]
  have hω1 : σ ζ * (ζ⁻¹) ^ q - 1 ∈ A.nonunits := by
    have hinvpow : (ζ⁻¹) ^ q * ζ ^ q = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hζ0, one_pow]
    have heq : σ ζ * (ζ⁻¹) ^ q - 1 = (ζ⁻¹) ^ q * (σ ζ - ζ ^ q) := by
      rw [mul_sub, hinvpow, mul_comm ((ζ⁻¹) ^ q) (σ ζ)]
    rw [heq]
    exact vs_mul_mem_nonunits (pow_mem hζinv q) hsub
  have hone : σ ζ * (ζ⁻¹) ^ q = 1 :=
    vs_eq_one_of_pow_eq_one_of_sub_one_mem_nonunits hm hωm hω1
  have hζq0 : ζ ^ q ≠ 0 := pow_ne_zero q hζ0
  rw [inv_pow, mul_inv_eq_one₀ hζq0] at hone
  exact hone

theorem frob_apply_eq_pow_of_pow_prime_pow_eq_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q ≠ p) (hA : A.LiesOverPrime q) {σ : L ≃ₐ[K] L} (hσ : A.IsFrobeniusAt σ q)
    (n : ℕ) {ζ : L} (hζ : ζ ^ p ^ n = 1) : σ ζ = ζ ^ q := by
  refine frob_apply_eq_pow_of_pow_eq_one hσ ?_ hζ
  refine vs_natCast_residueField_ne_zero_of_not_dvd hq hA fun hdvd => hqp ?_
  exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdvd)

theorem frob_pow_apply_eq_pow_of_pow_prime_pow_eq_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q ≠ p) (hA : A.LiesOverPrime q) {σ : L ≃ₐ[K] L} (hσ : A.IsFrobeniusAt σ q)
    (n : ℕ) {ζ : L} (hζ : ζ ^ p ^ n = 1) (j : ℕ) : (σ ^ j) ζ = ζ ^ q ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, AlgEquiv.mul_apply, frob_apply_eq_pow_of_pow_prime_pow_eq_one hp hq hqp hA hσ
      n hζ, map_pow, ih, ← pow_mul, ← pow_succ]

end Place

end DeskDd6

open DeskDd6 in

theorem solution
    {q : ℕ} (hq : q.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : A.IsFrobeniusAt σ q)
    {m : ℕ} (hm : ¬ q ∣ m) (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ m = 1) :
    σ ζ = ζ ^ q :=
  frob_apply_eq_pow_of_pow_eq_one hσ (vs_natCast_residueField_ne_zero_of_not_dvd hq hA hm) hζ

#print axioms solution

end S_ValuationSubring_IsFrobeniusAt_apply_rootOfUnity_eq_pow_of_not_dvd
end P2MW
export P2MW.S_ValuationSubring_IsFrobeniusAt_apply_rootOfUnity_eq_pow_of_not_dvd (solution)
