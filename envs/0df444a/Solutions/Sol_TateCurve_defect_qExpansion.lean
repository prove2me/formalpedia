-- Prove2me | solution 1 for TateCurve.defect_qExpansion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/05e44040-f13c-5ea1-a7ad-e5cd114c19e5

import Definitions.Def_TateCurve_Defect
import Theorems.Thm_TateCurve_pointX_qExpansion
import Theorems.Thm_TateCurve_pointY_qExpansion
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_defect_qExpansion

set_option autoImplicit false
open scoped NNReal
open IsUltrametricDist Filter

namespace TateCurve
p2m_export "TateCurve" "cauchyMul qSeries_mul summable_norm_cauchyMul summable_norm_qSeries xCoeffFull xCoeffFull_zero xCoeffFull_succ yCoeffFull yCoeffFull_zero yCoeffFull_succ a₄Coeff a₄Coeff_zero a₄Coeff_succ a₆Coeff a₆Coeff_zero a₆Coeff_succ norm_xCoeffFull_le norm_yCoeffFull_le norm_a₄Coeff_le norm_a₆Coeff_le defectCoeff pointX pointY term term_zero summable_term coeffSum b a₄ a₆ growthBound growthBound_nonneg pointX_qExpansion pointY_qExpansion"
p2m_open "TateCurve"

section GeneralRegrouping

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
variable {h : ℕ → K} {C : ℝ} {r : K}

private def pairTerm (h : ℕ → K) (r : K) (c : ℕ+ × ℕ+) : K :=
  h (c.2 : ℕ) * r ^ ((c.1 : ℕ) * (c.2 : ℕ))

private def sigmaTerm' (h : ℕ → K) (r : K)
    (x : (n : ℕ+) × {p // p ∈ (n : ℕ).divisorsAntidiagonal}) : K :=
  h x.2.1.2 * r ^ (x.2.1.1 * x.2.1.2)

private theorem norm_le_of_le_geometric (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m)
    {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ n.divisorsAntidiagonal) :
    ‖h p.2 * r ^ (p.1 * p.2)‖ ≤ C ^ n * ‖r‖ ^ n := by
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC1
  obtain ⟨hmul, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have hp2mem : p.2 ∈ n.divisors := Nat.snd_mem_divisors_of_mem_antidiagonal hp
  have hp2pos : 0 < p.2 := Nat.pos_of_mem_divisors hp2mem
  have hp2le : p.2 ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_divisors hp2mem)
  rw [norm_mul, norm_pow, hmul]
  exact mul_le_mul ((hh p.2 hp2pos).trans (pow_le_pow_right₀ hC1 hp2le)) le_rfl
    (pow_nonneg (norm_nonneg r) n) (pow_nonneg hC0 n)

private theorem summable_sigmaTerm' (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) :
    Summable (sigmaTerm' h r) := by
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC1
  have hs0 : (0 : ℝ) ≤ C * ‖r‖ := mul_nonneg hC0 (norm_nonneg r)
  have hs1 : C * ‖r‖ < 1 := by rwa [mul_comm] at hrC

  have hgeom : Summable fun n : ℕ => (n : ℝ) * (C * ‖r‖) ^ n := by
    have habs : ‖(C * ‖r‖ : ℝ)‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hs0]
    have := summable_pow_mul_geometric_of_norm_lt_one 1 habs
    simpa using this
  have hgeomP : Summable fun n : ℕ+ => ((n : ℕ) : ℝ) * (C * ‖r‖) ^ (n : ℕ) :=
    hgeom.comp_injective PNat.coe_injective
  apply Summable.of_norm
  rw [summable_sigma_of_nonneg (fun a => norm_nonneg _)]
  refine ⟨fun n => (hasSum_fintype _).summable, ?_⟩
  refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun x => norm_nonneg _)
    (fun n => ?_) hgeomP
  rw [tsum_fintype]
  calc ∑ x : {p // p ∈ ((n : ℕ)).divisorsAntidiagonal}, ‖sigmaTerm' h r ⟨n, x⟩‖
      = ∑ p ∈ ((n : ℕ)).divisorsAntidiagonal, ‖h p.2 * r ^ (p.1 * p.2)‖ := by
        rw [Finset.univ_eq_attach]
        exact Finset.sum_attach ((n : ℕ)).divisorsAntidiagonal fun p => ‖h p.2 * r ^ (p.1 * p.2)‖
    _ ≤ ∑ _p ∈ ((n : ℕ)).divisorsAntidiagonal, C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ) :=
        Finset.sum_le_sum fun p hp => norm_le_of_le_geometric hC1 hh hp
    _ = ∑ _d ∈ ((n : ℕ)).divisors, C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ) := by
        rw [Nat.sum_divisorsAntidiagonal' (f := fun _ _ => C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ))]
    _ = (((n : ℕ)).divisors.card : ℝ) * (C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((n : ℕ) : ℝ) * (C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ)) := by
        refine mul_le_mul_of_nonneg_right ?_
          (mul_nonneg (pow_nonneg hC0 _) (pow_nonneg (norm_nonneg r) _))
        exact_mod_cast Nat.card_divisors_le_self (n : ℕ)
    _ = ((n : ℕ) : ℝ) * (C * ‖r‖) ^ (n : ℕ) := by rw [mul_pow]

private theorem summable_pairTerm (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) :
    Summable (pairTerm h r) := by
  have hcomp : Summable (pairTerm h r ∘ ⇑sigmaAntidiagonalEquivProd) := by
    have hfun : pairTerm h r ∘ ⇑sigmaAntidiagonalEquivProd = sigmaTerm' h r := by
      funext x
      obtain ⟨n, ⟨⟨a, b⟩, hab⟩⟩ := x
      rfl
    rw [hfun]
    exact summable_sigmaTerm' hC1 hh hrC
  exact (Equiv.summable_iff sigmaAntidiagonalEquivProd).mp hcomp

private theorem tsum_pairTerm_eq_tsum_divisors (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) :
    ∑' c : ℕ+ × ℕ+, pairTerm h r c
      = ∑' n : ℕ+, (∑ d ∈ (n : ℕ).divisors, h d) * r ^ (n : ℕ) := by
  have haux := summable_sigmaTerm' (r := r) hC1 hh hrC

  have htrans : ∑' c : ℕ+ × ℕ+, pairTerm h r c
      = ∑' x : (n : ℕ+) × {p // p ∈ (n : ℕ).divisorsAntidiagonal}, sigmaTerm' h r x := by
    rw [← Equiv.tsum_eq sigmaAntidiagonalEquivProd (pairTerm h r)]
    refine tsum_congr fun x => ?_
    obtain ⟨n, ⟨⟨a, b⟩, hab⟩⟩ := x
    rfl
  rw [htrans, Summable.tsum_sigma haux]
  refine tsum_congr fun n => ?_

  rw [tsum_fintype]
  calc ∑ x : {p // p ∈ ((n : ℕ)).divisorsAntidiagonal}, sigmaTerm' h r ⟨n, x⟩
      = ∑ p ∈ ((n : ℕ)).divisorsAntidiagonal, h p.2 * r ^ (p.1 * p.2) := by
        rw [Finset.univ_eq_attach]
        exact Finset.sum_attach ((n : ℕ)).divisorsAntidiagonal fun p => h p.2 * r ^ (p.1 * p.2)
    _ = ∑ p ∈ ((n : ℕ)).divisorsAntidiagonal, h p.2 * r ^ (n : ℕ) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
    _ = (∑ p ∈ ((n : ℕ)).divisorsAntidiagonal, h p.2) * r ^ (n : ℕ) := by
        rw [Finset.sum_mul]
    _ = (∑ d ∈ ((n : ℕ)).divisors, h d) * r ^ (n : ℕ) := by
        rw [Nat.sum_divisorsAntidiagonal' (f := fun _ d => h d)]

private def succEquivPNat : ℕ ≃ ℕ+ where
  toFun n := n.succPNat
  invFun n := n.natPred
  left_inv n := Nat.natPred_succPNat n
  right_inv n := PNat.succPNat_natPred n

private theorem tsum_succ_prod_loc (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) :
    ∑' p : ℕ × ℕ, h (p.2 + 1) * r ^ ((p.1 + 1) * (p.2 + 1))
      = ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, h d) * r ^ (N + 1) := by
  have hL : ∑' p : ℕ × ℕ, h (p.2 + 1) * r ^ ((p.1 + 1) * (p.2 + 1))
      = ∑' c : ℕ+ × ℕ+, pairTerm h r c := by
    rw [← Equiv.tsum_eq (Equiv.prodCongr succEquivPNat succEquivPNat) (pairTerm h r)]
    refine tsum_congr fun p => ?_
    obtain ⟨a, b⟩ := p
    rfl
  have hR : ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, h d) * r ^ (N + 1)
      = ∑' n : ℕ+, (∑ d ∈ (n : ℕ).divisors, h d) * r ^ (n : ℕ) := by
    rw [← Equiv.tsum_eq succEquivPNat
      (fun n : ℕ+ => (∑ d ∈ (n : ℕ).divisors, h d) * r ^ (n : ℕ))]
    exact tsum_congr fun N => rfl
  rw [hL, hR]
  exact tsum_pairTerm_eq_tsum_divisors hC1 hh hrC

private theorem summable_succ_prod_loc (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) :
    Summable fun p : ℕ × ℕ => h (p.2 + 1) * r ^ ((p.1 + 1) * (p.2 + 1)) := by
  have hsum := summable_pairTerm (r := r) hC1 hh hrC
  have hcomp : Summable (pairTerm h r ∘ ⇑(Equiv.prodCongr succEquivPNat succEquivPNat)) :=
    (Equiv.summable_iff (Equiv.prodCongr succEquivPNat succEquivPNat)).mpr hsum
  refine hcomp.congr fun p => ?_
  obtain ⟨a, b⟩ := p
  rfl

end GeneralRegrouping

section AnnulusBound
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] {q u : K}
private theorem norm_mul_growthBound_lt_one (hq : ‖q‖₊ < 1) (hqu : ‖q * u‖₊ < 1)
    (hqu' : ‖q * u⁻¹‖₊ < 1) : ‖q‖ * growthBound u < 1 := by
  have h1 : ‖q‖ * ‖u‖ < 1 := by
    have h : ‖q * u‖ < 1 := hqu
    rwa [norm_mul] at h
  have h2 : ‖q‖ * ‖u⁻¹‖ < 1 := by
    have h : ‖q * u⁻¹‖ < 1 := hqu'
    rwa [norm_mul] at h
  have h3 : ‖q‖ < 1 := hq
  rw [growthBound, mul_max_of_nonneg _ _ (norm_nonneg q),
    mul_max_of_nonneg _ _ (norm_nonneg q), mul_one]
  exact max_lt (max_lt h1 h2) h3
end AnnulusBound

section CoeffSumExpansion

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K}

private theorem hasSum_term_succ (c : ℕ → ℕ) (hq : ‖q‖₊ < 1) (n : ℕ) :
    HasSum (fun m : ℕ => ((c (n + 1) : K)) * q ^ ((m + 1) * (n + 1))) (term c q (n + 1)) := by
  have hqn : ‖q ^ (n + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) (show ‖q‖ < 1 from hq) (Nat.succ_ne_zero n)
  have h2 := (hasSum_geometric_of_norm_lt_one hqn).mul_left ((c (n + 1) : K) * q ^ (n + 1))
  have hfun : (fun m : ℕ => (c (n + 1) : K) * q ^ (n + 1) * (q ^ (n + 1)) ^ m)
      = fun m : ℕ => ((c (n + 1) : K)) * q ^ ((m + 1) * (n + 1)) := by
    funext m
    rw [Nat.mul_comm (m + 1) (n + 1), pow_mul, pow_succ]
    ring
  rw [hfun] at h2
  have hval : (c (n + 1) : K) * q ^ (n + 1) * (1 - q ^ (n + 1))⁻¹ = term c q (n + 1) := by
    rw [term, div_eq_mul_inv]
    ring
  rwa [hval] at h2

private theorem coeffSum_qExpansion (c : ℕ → ℕ) (hq : ‖q‖₊ < 1) :
    coeffSum c q = ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, (c d : K)) * q ^ (N + 1) := by
  have hC1 : (1 : ℝ) ≤ 1 := le_refl 1
  have hh : ∀ m : ℕ, 0 < m → ‖((c m : ℕ) : K)‖ ≤ (1 : ℝ) ^ m := fun m _ => by
    rw [one_pow]; exact IsUltrametricDist.norm_natCast_le_one K (c m)
  have hrC : ‖q‖ * 1 < 1 := by rw [mul_one]; exact_mod_cast hq

  have hengine := tsum_succ_prod_loc (h := fun d => (c d : K)) (r := q) hC1 hh hrC
  have hdouble : Summable fun p : ℕ × ℕ => ((c (p.2 + 1) : K)) * q ^ ((p.1 + 1) * (p.2 + 1)) :=
    (summable_succ_prod_loc (h := fun d => (c d : K)) (r := q) hC1 hh hrC).congr fun p => rfl
  have hGsum : Summable fun p : ℕ × ℕ => ((c (p.1 + 1) : K)) * q ^ ((p.2 + 1) * (p.1 + 1)) :=
    ((Equiv.summable_iff (Equiv.prodComm ℕ ℕ)).mpr hdouble).congr fun p => rfl

  have hA : coeffSum c q = ∑' n : ℕ, term c q (n + 1) := by
    rw [coeffSum, (summable_term c hq).tsum_eq_zero_add, term_zero, zero_add]
  have hB : ∑' n : ℕ, term c q (n + 1)
      = ∑' n : ℕ, ∑' m : ℕ, ((c (n + 1) : K)) * q ^ ((m + 1) * (n + 1)) :=
    tsum_congr fun n => ((hasSum_term_succ c hq n).tsum_eq).symm
  have hC : ∑' n : ℕ, ∑' m : ℕ, ((c (n + 1) : K)) * q ^ ((m + 1) * (n + 1))
      = ∑' p : ℕ × ℕ, ((c (p.1 + 1) : K)) * q ^ ((p.2 + 1) * (p.1 + 1)) :=
    (hGsum.tsum_prod).symm
  have hD : ∑' p : ℕ × ℕ, ((c (p.1 + 1) : K)) * q ^ ((p.2 + 1) * (p.1 + 1))
      = ∑' p : ℕ × ℕ, ((c (p.2 + 1) : K)) * q ^ ((p.1 + 1) * (p.2 + 1)) :=
    Equiv.tsum_eq (Equiv.prodComm ℕ ℕ)
      (fun p : ℕ × ℕ => ((c (p.2 + 1) : K)) * q ^ ((p.1 + 1) * (p.2 + 1)))
  rw [hA, hB, hC, hD]
  exact hengine

private theorem summable_norm_a₄Series (hq : ‖q‖₊ < 1) :
    Summable fun N => ‖a₄Coeff (K := K) N * q ^ N‖ := by
  refine summable_norm_qSeries (B := 1) (C := 1) zero_le_one (fun N => ?_)
    (by rw [mul_one]; exact_mod_cast hq)
  rw [one_mul, one_pow]
  exact norm_a₄Coeff_le N

private theorem summable_norm_a₆Series (hq : ‖q‖₊ < 1) :
    Summable fun N => ‖a₆Coeff (K := K) N * q ^ N‖ := by
  refine summable_norm_qSeries (B := 1) (C := 1) zero_le_one (fun N => ?_)
    (by rw [mul_one]; exact_mod_cast hq)
  rw [one_mul, one_pow]
  exact norm_a₆Coeff_le N

variable {u : K}

private theorem summable_norm_xSeries (hq : ‖q‖₊ < 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) :
    Summable fun N => ‖xCoeffFull u N * q ^ N‖ :=
  summable_norm_qSeries (growthBound_nonneg u) (norm_xCoeffFull_le u)
    (norm_mul_growthBound_lt_one hq hqu hqu')

private theorem summable_norm_ySeries (hq : ‖q‖₊ < 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) :
    Summable fun N => ‖yCoeffFull u N * q ^ N‖ :=
  summable_norm_qSeries (growthBound_nonneg u) (norm_yCoeffFull_le u)
    (norm_mul_growthBound_lt_one hq hqu hqu')

private theorem pointX_eq_tsum (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) :
    pointX q u = ∑' N : ℕ, xCoeffFull u N * q ^ N := by
  have hsum : Summable fun N => xCoeffFull u N * q ^ N :=
    (summable_norm_xSeries hq hqu hqu').of_norm
  rw [hsum.tsum_eq_zero_add]
  simp only [xCoeffFull_zero, xCoeffFull_succ, pow_zero, mul_one]
  exact TateCurve.pointX_qExpansion hq0 hq hu0 hu hqu hqu'

private theorem pointY_eq_tsum (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) :
    pointY q u = ∑' N : ℕ, yCoeffFull u N * q ^ N := by
  have hsum : Summable fun N => yCoeffFull u N * q ^ N :=
    (summable_norm_ySeries hq hqu hqu').of_norm
  rw [hsum.tsum_eq_zero_add]
  simp only [yCoeffFull_zero, yCoeffFull_succ, pow_zero, mul_one]
  exact TateCurve.pointY_qExpansion hq0 hq hu0 hu hqu hqu'

private theorem a₄_eq_tsum (hq : ‖q‖₊ < 1) : a₄ q = ∑' N : ℕ, a₄Coeff (K := K) N * q ^ N := by
  have hsum : Summable fun N => a₄Coeff (K := K) N * q ^ N := (summable_norm_a₄Series hq).of_norm
  rw [hsum.tsum_eq_zero_add]
  simp only [a₄Coeff_zero, a₄Coeff_succ, zero_mul, zero_add]
  have hexp : ∑' N : ℕ, (-(∑ d ∈ (N + 1).divisors, ((5 * d ^ 3 : ℕ) : K))) * q ^ (N + 1)
      = -(∑' N : ℕ, (∑ d ∈ (N + 1).divisors, ((5 * d ^ 3 : ℕ) : K)) * q ^ (N + 1)) := by
    rw [← tsum_neg]
    exact tsum_congr fun N => by rw [neg_mul]
  rw [hexp, ← coeffSum_qExpansion (fun n => 5 * n ^ 3) hq, a₄]

private theorem a₆_eq_tsum (hq : ‖q‖₊ < 1) : a₆ q = ∑' N : ℕ, a₆Coeff (K := K) N * q ^ N := by
  have hsum : Summable fun N => a₆Coeff (K := K) N * q ^ N := (summable_norm_a₆Series hq).of_norm
  rw [hsum.tsum_eq_zero_add]
  simp only [a₆Coeff_zero, a₆Coeff_succ, zero_mul, zero_add]
  have hexp : ∑' N : ℕ, (-(∑ d ∈ (N + 1).divisors, ((b d : ℕ) : K))) * q ^ (N + 1)
      = -(∑' N : ℕ, (∑ d ∈ (N + 1).divisors, ((b d : ℕ) : K)) * q ^ (N + 1)) := by
    rw [← tsum_neg]
    exact tsum_congr fun N => by rw [neg_mul]
  rw [hexp, ← coeffSum_qExpansion b hq, a₆]

end CoeffSumExpansion

section MainProof

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q u : K}

private theorem defect_qExpansion_loc (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) :
    pointY q u ^ 2 + pointX q u * pointY q u
      - (pointX q u ^ 3 + a₄ q * pointX q u + a₆ q)
      = ∑' N : ℕ, defectCoeff u N * q ^ N := by

  have hXn := summable_norm_xSeries (u := u) hq hqu hqu'
  have hYn := summable_norm_ySeries (u := u) hq hqu hqu'
  have hA4n := summable_norm_a₄Series (K := K) hq
  have hA6n := summable_norm_a₆Series (K := K) hq
  have hXXn := summable_norm_cauchyMul hXn hXn

  have hX := pointX_eq_tsum hq0 hq hu0 hu hqu hqu'
  have hY := pointY_eq_tsum hq0 hq hu0 hu hqu hqu'
  have hA4 := a₄_eq_tsum (K := K) hq
  have hA6 := a₆_eq_tsum (K := K) hq

  have hYY : pointY q u ^ 2
      = ∑' N : ℕ, cauchyMul (yCoeffFull u) (yCoeffFull u) N * q ^ N := by
    rw [pow_two, hY, qSeries_mul hYn hYn]
  have hXY : pointX q u * pointY q u
      = ∑' N : ℕ, cauchyMul (xCoeffFull u) (yCoeffFull u) N * q ^ N := by
    rw [hX, hY, qSeries_mul hXn hYn]
  have hXX : pointX q u * pointX q u
      = ∑' N : ℕ, cauchyMul (xCoeffFull u) (xCoeffFull u) N * q ^ N := by
    rw [hX, qSeries_mul hXn hXn]
  have hX3 : pointX q u ^ 3
      = ∑' N : ℕ, cauchyMul (xCoeffFull u) (cauchyMul (xCoeffFull u) (xCoeffFull u)) N * q ^ N := by
    rw [show pointX q u ^ 3 = pointX q u * (pointX q u * pointX q u) by ring, hXX, hX,
      qSeries_mul hXn hXXn]
  have hA4X : a₄ q * pointX q u
      = ∑' N : ℕ, cauchyMul a₄Coeff (xCoeffFull u) N * q ^ N := by
    rw [hA4, hX, qSeries_mul hA4n hXn]

  have sYY : Summable fun N => cauchyMul (yCoeffFull u) (yCoeffFull u) N * q ^ N :=
    (summable_norm_cauchyMul hYn hYn).of_norm
  have sXY : Summable fun N => cauchyMul (xCoeffFull u) (yCoeffFull u) N * q ^ N :=
    (summable_norm_cauchyMul hXn hYn).of_norm
  have sX3 : Summable fun N =>
      cauchyMul (xCoeffFull u) (cauchyMul (xCoeffFull u) (xCoeffFull u)) N * q ^ N :=
    (summable_norm_cauchyMul hXn hXXn).of_norm
  have sA4X : Summable fun N => cauchyMul a₄Coeff (xCoeffFull u) N * q ^ N :=
    (summable_norm_cauchyMul hA4n hXn).of_norm
  have sA6 : Summable fun N => a₆Coeff (K := K) N * q ^ N := hA6n.of_norm

  have tsum_add_combine : ∀ {f g : ℕ → K}, (Summable fun N => f N * q ^ N) →
      (Summable fun N => g N * q ^ N) →
      (∑' N : ℕ, f N * q ^ N) + (∑' N : ℕ, g N * q ^ N) = ∑' N : ℕ, (f N + g N) * q ^ N := by
    intro f g hf hg
    rw [← hf.tsum_add hg]
    exact tsum_congr fun N => (add_mul _ _ _).symm
  have tsum_sub_combine : ∀ {f g : ℕ → K}, (Summable fun N => f N * q ^ N) →
      (Summable fun N => g N * q ^ N) →
      (∑' N : ℕ, f N * q ^ N) - (∑' N : ℕ, g N * q ^ N) = ∑' N : ℕ, (f N - g N) * q ^ N := by
    intro f g hf hg
    rw [← hf.tsum_sub hg]
    exact tsum_congr fun N => (sub_mul _ _ _).symm

  rw [hYY, hXY, hX3, hA4X, hA6,
    tsum_add_combine sYY sXY, tsum_add_combine sX3 sA4X,
    tsum_add_combine ((sX3.add sA4X).congr fun N => (add_mul _ _ _).symm) sA6,
    tsum_sub_combine ((sYY.add sXY).congr fun N => (add_mul _ _ _).symm)
      (((sX3.add sA4X).congr fun N => (add_mul _ _ _).symm).add sA6 |>.congr
        fun N => (add_mul _ _ _).symm)]
  exact tsum_congr fun N => by rw [defectCoeff]

end MainProof

end TateCurve

p2m_open "TateCurve P2MW.S_TateCurve_defect_qExpansion.TateCurve"

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) :
    pointY q u ^ 2 + pointX q u * pointY q u
      - (pointX q u ^ 3 + a₄ q * pointX q u + a₆ q)
      = ∑' N : ℕ, defectCoeff u N * q ^ N :=
  defect_qExpansion_loc hq0 hq hu0 hu hqu hqu'

end S_TateCurve_defect_qExpansion
end P2MW
export P2MW.S_TateCurve_defect_qExpansion (solution)
