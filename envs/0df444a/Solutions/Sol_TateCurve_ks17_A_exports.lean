-- Prove2me | solution 1 for TateCurve.ks17_A_exports
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b11a39b2-731f-5aca-b84b-f5a86f466ebf

import Mathlib
import Definitions.Def_TateCurve_XMultIdentities
import Definitions.Def_TateCurve_DefectLines
import Definitions.Def_NumberTheory_DivisorConvolution
import Definitions.Def_TateCurve_KeystoneVocab

import Theorems.Thm_TateCurve_pointX_inv
import Theorems.Thm_TateCurve_pointX_q_mul
import Theorems.Thm_TateCurve_pointX_zpow_mul
import Theorems.Thm_TateCurve_defectCoeff_one
import Theorems.Thm_TateCurve_pointX_qExpansion
import Theorems.Thm_TateCurve_pointY_qExpansion
import Theorems.Thm_TateCurve_pointY_q_mul
import Theorems.Thm_TateCurve_pointY_inv
import Theorems.Thm_TateCurve_pointY_zpow_mul
import Theorems.Thm_TateCurve_exists_zpow_mul_mem_annulus
import Theorems.Thm_TateCurve_equation_pointX_pointY_of_defectCoeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_ks17_A_exports

universe u_1

namespace TateCurve
p2m_export "TateCurve" "eq_zero_of_master_rows unitSpectator norm_unitSpectator unitSpectator_ne_one spectatorRows norm_spectatorRows_le symAdd_sum_of_laurentRows symAdd_prod_of_laurentRows symSumNum symProdNum OffLattice OffLattice.zpow_mul OffLattice.inv AddParams AddParams.swap pointX_inv_mul pointX_inv_mul_inv pointX_q_inv_mul addDefectSum addDefectProd addDefectSum_q_mul_left addDefectProd_q_mul_left nodal_symSum offLattice_of_norm_eq_one addParams_of_norm_one_spectator norm_mul_eq_of_norm_eq_one norm_mul_inv_eq_of_norm_eq_one specTail specAlpha specGamma summable_specTail_term norm_specTail_le spec_eq_zero_of_master summable_norm_a₄Series summable_norm_a₆Series summable_norm_xSeries summable_norm_ySeries ne_zero_of_one_lt_norm norm_q_lt_one_of_qshift norm_inv_lt_one_of_one_lt_norm cauchyMul_two tent xfun_mul_Fz_eq_tent cauchyMul cauchyMul_zero cauchyMul_one qSeries_mul summable_norm_cauchyMul xCoeffFull xCoeffFull_zero xCoeffFull_succ yCoeffFull yCoeffFull_zero yCoeffFull_succ a₄Coeff a₄Coeff_zero a₄Coeff_succ a₆Coeff a₆Coeff_zero a₆Coeff_succ xfun yfun pointX pointY term term_zero summable_term coeffSum b a₄ a₆ curve curve_a₁ curve_a₃ xDivTerm yDivTerm xCoeff yCoeff pointX_inv pointX_q_mul pointX_zpow_mul pointPsiTwo addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff psiCoeffFull addDefectDiffCoeff LatticeRep OnHalfLattice MuTranslation pointX_qExpansion pointY_qExpansion pointY_q_mul pointY_inv pointY_zpow_mul"
p2m_open "TateCurve~tsum_succ_prod_eq_tsum_divisors"

section GeneralRegrouping

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
variable {h : ℕ → K} {C : ℝ} {r : K}

private def pairTerm_A0 (h : ℕ → K) (r : K) (c : ℕ+ × ℕ+) : K :=
  h (c.2 : ℕ) * r ^ ((c.1 : ℕ) * (c.2 : ℕ))

private def sigmaTerm'_A0 (h : ℕ → K) (r : K)
    (x : (n : ℕ+) × {p // p ∈ (n : ℕ).divisorsAntidiagonal}) : K :=
  h x.2.1.2 * r ^ (x.2.1.1 * x.2.1.2)

private theorem norm_le_of_le_geometric_A0 (hC1 : 1 ≤ C)
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

private theorem summable_sigmaTerm'_A0 (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) :
    Summable (sigmaTerm'_A0 h r) := by
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
  calc ∑ x : {p // p ∈ ((n : ℕ)).divisorsAntidiagonal}, ‖sigmaTerm'_A0 h r ⟨n, x⟩‖
      = ∑ p ∈ ((n : ℕ)).divisorsAntidiagonal, ‖h p.2 * r ^ (p.1 * p.2)‖ := by
        rw [Finset.univ_eq_attach]
        exact Finset.sum_attach ((n : ℕ)).divisorsAntidiagonal fun p => ‖h p.2 * r ^ (p.1 * p.2)‖
    _ ≤ ∑ _p ∈ ((n : ℕ)).divisorsAntidiagonal, C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ) :=
        Finset.sum_le_sum fun p hp => norm_le_of_le_geometric_A0 hC1 hh hp
    _ = ∑ _d ∈ ((n : ℕ)).divisors, C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ) := by
        rw [Nat.sum_divisorsAntidiagonal' (f := fun _ _ => C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ))]
    _ = (((n : ℕ)).divisors.card : ℝ) * (C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((n : ℕ) : ℝ) * (C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ)) := by
        refine mul_le_mul_of_nonneg_right ?_
          (mul_nonneg (pow_nonneg hC0 _) (pow_nonneg (norm_nonneg r) _))
        exact_mod_cast Nat.card_divisors_le_self (n : ℕ)
    _ = ((n : ℕ) : ℝ) * (C * ‖r‖) ^ (n : ℕ) := by rw [mul_pow]

private theorem summable_pairTerm_A0 (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) :
    Summable (pairTerm_A0 h r) := by
  have hcomp : Summable (pairTerm_A0 h r ∘ ⇑sigmaAntidiagonalEquivProd) := by
    have hfun : pairTerm_A0 h r ∘ ⇑sigmaAntidiagonalEquivProd = sigmaTerm'_A0 h r := by
      funext x
      obtain ⟨n, ⟨⟨a, b⟩, hab⟩⟩ := x
      rfl
    rw [hfun]
    exact summable_sigmaTerm'_A0 hC1 hh hrC
  exact (Equiv.summable_iff sigmaAntidiagonalEquivProd).mp hcomp

private theorem tsum_pairTerm_eq_tsum_divisors_A0 (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) :
    ∑' c : ℕ+ × ℕ+, pairTerm_A0 h r c
      = ∑' n : ℕ+, (∑ d ∈ (n : ℕ).divisors, h d) * r ^ (n : ℕ) := by
  have haux := summable_sigmaTerm'_A0 (r := r) hC1 hh hrC

  have htrans : ∑' c : ℕ+ × ℕ+, pairTerm_A0 h r c
      = ∑' x : (n : ℕ+) × {p // p ∈ (n : ℕ).divisorsAntidiagonal}, sigmaTerm'_A0 h r x := by
    rw [← Equiv.tsum_eq sigmaAntidiagonalEquivProd (pairTerm_A0 h r)]
    refine tsum_congr fun x => ?_
    obtain ⟨n, ⟨⟨a, b⟩, hab⟩⟩ := x
    rfl
  rw [htrans, Summable.tsum_sigma haux]
  refine tsum_congr fun n => ?_

  rw [tsum_fintype]
  calc ∑ x : {p // p ∈ ((n : ℕ)).divisorsAntidiagonal}, sigmaTerm'_A0 h r ⟨n, x⟩
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

private def succEquivPNat_A0 : ℕ ≃ ℕ+ where
  toFun n := n.succPNat
  invFun n := n.natPred
  left_inv n := Nat.natPred_succPNat n
  right_inv n := PNat.succPNat_natPred n

theorem tsum_succ_prod_eq_tsum_divisors (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) :
    ∑' p : ℕ × ℕ, h (p.2 + 1) * r ^ ((p.1 + 1) * (p.2 + 1))
      = ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, h d) * r ^ (N + 1) := by
  have hL : ∑' p : ℕ × ℕ, h (p.2 + 1) * r ^ ((p.1 + 1) * (p.2 + 1))
      = ∑' c : ℕ+ × ℕ+, pairTerm_A0 h r c := by
    rw [← Equiv.tsum_eq (Equiv.prodCongr succEquivPNat_A0 succEquivPNat_A0) (pairTerm_A0 h r)]
    refine tsum_congr fun p => ?_
    obtain ⟨a, b⟩ := p
    rfl
  have hR : ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, h d) * r ^ (N + 1)
      = ∑' n : ℕ+, (∑ d ∈ (n : ℕ).divisors, h d) * r ^ (n : ℕ) := by
    rw [← Equiv.tsum_eq succEquivPNat_A0
      (fun n : ℕ+ => (∑ d ∈ (n : ℕ).divisors, h d) * r ^ (n : ℕ))]
    exact tsum_congr fun N => rfl
  rw [hL, hR]
  exact tsum_pairTerm_eq_tsum_divisors_A0 hC1 hh hrC

theorem summable_succ_prod (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) :
    Summable fun p : ℕ × ℕ => h (p.2 + 1) * r ^ ((p.1 + 1) * (p.2 + 1)) := by
  have hsum := summable_pairTerm_A0 (r := r) hC1 hh hrC
  have hcomp : Summable (pairTerm_A0 h r ∘ ⇑(Equiv.prodCongr succEquivPNat_A0 succEquivPNat_A0)) :=
    (Equiv.summable_iff (Equiv.prodCongr succEquivPNat_A0 succEquivPNat_A0)).mpr hsum
  refine hcomp.congr fun p => ?_
  obtain ⟨a, b⟩ := p
  rfl

end GeneralRegrouping

section CoeffSumExpansion

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K}

private theorem hasSum_term_succ_A0 (c : ℕ → ℕ) (hq : ‖q‖₊ < 1) (n : ℕ) :
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

theorem coeffSum_qExpansion (c : ℕ → ℕ) (hq : ‖q‖₊ < 1) :
    coeffSum c q = ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, (c d : K)) * q ^ (N + 1) := by
  have hC1 : (1 : ℝ) ≤ 1 := le_refl 1
  have hh : ∀ m : ℕ, 0 < m → ‖((c m : ℕ) : K)‖ ≤ (1 : ℝ) ^ m := fun m _ => by
    rw [one_pow]; exact IsUltrametricDist.norm_natCast_le_one K (c m)
  have hrC : ‖q‖ * 1 < 1 := by rw [mul_one]; exact_mod_cast hq

  have hengine := tsum_succ_prod_eq_tsum_divisors (h := fun d => (c d : K)) (r := q) hC1 hh hrC
  have hdouble : Summable fun p : ℕ × ℕ => ((c (p.2 + 1) : K)) * q ^ ((p.1 + 1) * (p.2 + 1)) :=
    (summable_succ_prod (h := fun d => (c d : K)) (r := q) hC1 hh hrC).congr fun p => rfl
  have hGsum : Summable fun p : ℕ × ℕ => ((c (p.1 + 1) : K)) * q ^ ((p.2 + 1) * (p.1 + 1)) :=
    ((Equiv.summable_iff (Equiv.prodComm ℕ ℕ)).mpr hdouble).congr fun p => rfl

  have hA : coeffSum c q = ∑' n : ℕ, term c q (n + 1) := by
    rw [coeffSum, (summable_term c hq).tsum_eq_zero_add, term_zero, zero_add]
  have hB : ∑' n : ℕ, term c q (n + 1)
      = ∑' n : ℕ, ∑' m : ℕ, ((c (n + 1) : K)) * q ^ ((m + 1) * (n + 1)) :=
    tsum_congr fun n => ((hasSum_term_succ_A0 c hq n).tsum_eq).symm
  have hC : ∑' n : ℕ, ∑' m : ℕ, ((c (n + 1) : K)) * q ^ ((m + 1) * (n + 1))
      = ∑' p : ℕ × ℕ, ((c (p.1 + 1) : K)) * q ^ ((p.2 + 1) * (p.1 + 1)) :=
    (hGsum.tsum_prod).symm
  have hD : ∑' p : ℕ × ℕ, ((c (p.1 + 1) : K)) * q ^ ((p.2 + 1) * (p.1 + 1))
      = ∑' p : ℕ × ℕ, ((c (p.2 + 1) : K)) * q ^ ((p.1 + 1) * (p.2 + 1)) :=
    Equiv.tsum_eq (Equiv.prodComm ℕ ℕ)
      (fun p : ℕ × ℕ => ((c (p.2 + 1) : K)) * q ^ ((p.1 + 1) * (p.2 + 1)))
  rw [hA, hB, hC, hD]
  exact hengine

variable {u : K}

theorem pointX_eq_tsum (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) :
    pointX q u = ∑' N : ℕ, xCoeffFull u N * q ^ N := by
  have hsum : Summable fun N => xCoeffFull u N * q ^ N :=
    (summable_norm_xSeries hq hqu hqu').of_norm
  rw [hsum.tsum_eq_zero_add]
  simp only [xCoeffFull_zero, xCoeffFull_succ, pow_zero, mul_one]
  exact pointX_qExpansion hq0 hq hu0 hu hqu hqu'

theorem pointY_eq_tsum (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) :
    pointY q u = ∑' N : ℕ, yCoeffFull u N * q ^ N := by
  have hsum : Summable fun N => yCoeffFull u N * q ^ N :=
    (summable_norm_ySeries hq hqu hqu').of_norm
  rw [hsum.tsum_eq_zero_add]
  simp only [yCoeffFull_zero, yCoeffFull_succ, pow_zero, mul_one]
  exact pointY_qExpansion hq0 hq hu0 hu hqu hqu'

theorem a₄_eq_tsum (hq : ‖q‖₊ < 1) : a₄ q = ∑' N : ℕ, a₄Coeff (K := K) N * q ^ N := by
  have hsum : Summable fun N => a₄Coeff (K := K) N * q ^ N := (summable_norm_a₄Series hq).of_norm
  rw [hsum.tsum_eq_zero_add]
  simp only [a₄Coeff_zero, a₄Coeff_succ, zero_mul, zero_add]
  have hexp : ∑' N : ℕ, (-(∑ d ∈ (N + 1).divisors, ((5 * d ^ 3 : ℕ) : K))) * q ^ (N + 1)
      = -(∑' N : ℕ, (∑ d ∈ (N + 1).divisors, ((5 * d ^ 3 : ℕ) : K)) * q ^ (N + 1)) := by
    rw [← tsum_neg]
    exact tsum_congr fun N => by rw [neg_mul]
  rw [hexp, ← coeffSum_qExpansion (fun n => 5 * n ^ 3) hq, a₄]

theorem a₆_eq_tsum (hq : ‖q‖₊ < 1) : a₆ q = ∑' N : ℕ, a₆Coeff (K := K) N * q ^ N := by
  have hsum : Summable fun N => a₆Coeff (K := K) N * q ^ N := (summable_norm_a₆Series hq).of_norm
  rw [hsum.tsum_eq_zero_add]
  simp only [a₆Coeff_zero, a₆Coeff_succ, zero_mul, zero_add]
  have hexp : ∑' N : ℕ, (-(∑ d ∈ (N + 1).divisors, ((b d : ℕ) : K))) * q ^ (N + 1)
      = -(∑' N : ℕ, (∑ d ∈ (N + 1).divisors, ((b d : ℕ) : K)) * q ^ (N + 1)) := by
    rw [← tsum_neg]
    exact tsum_congr fun N => by rw [neg_mul]
  rw [hexp, ← coeffSum_qExpansion b hq, a₆]

end CoeffSumExpansion

end TateCurve

set_option autoImplicit false

set_option linter.unusedSectionVars false

open scoped NNReal
open IsUltrametricDist Filter Finset

namespace TateCurve
p2m_export "TateCurve" "eq_zero_of_master_rows unitSpectator norm_unitSpectator unitSpectator_ne_one spectatorRows norm_spectatorRows_le symAdd_sum_of_laurentRows symAdd_prod_of_laurentRows symSumNum symProdNum OffLattice OffLattice.zpow_mul OffLattice.inv AddParams AddParams.swap pointX_inv_mul pointX_inv_mul_inv pointX_q_inv_mul addDefectSum addDefectProd addDefectSum_q_mul_left addDefectProd_q_mul_left nodal_symSum offLattice_of_norm_eq_one addParams_of_norm_one_spectator norm_mul_eq_of_norm_eq_one norm_mul_inv_eq_of_norm_eq_one specTail specAlpha specGamma summable_specTail_term norm_specTail_le spec_eq_zero_of_master summable_norm_a₄Series summable_norm_a₆Series summable_norm_xSeries summable_norm_ySeries ne_zero_of_one_lt_norm norm_q_lt_one_of_qshift norm_inv_lt_one_of_one_lt_norm cauchyMul_two tent xfun_mul_Fz_eq_tent cauchyMul cauchyMul_zero cauchyMul_one qSeries_mul summable_norm_cauchyMul xCoeffFull xCoeffFull_zero xCoeffFull_succ yCoeffFull yCoeffFull_zero yCoeffFull_succ a₄Coeff a₄Coeff_zero a₄Coeff_succ a₆Coeff a₆Coeff_zero a₆Coeff_succ xfun yfun pointX pointY term term_zero summable_term coeffSum b a₄ a₆ curve curve_a₁ curve_a₃ xDivTerm yDivTerm xCoeff yCoeff pointX_inv pointX_q_mul pointX_zpow_mul pointPsiTwo addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff psiCoeffFull addDefectDiffCoeff LatticeRep OnHalfLattice MuTranslation pointX_qExpansion pointY_qExpansion pointY_q_mul pointY_inv pointY_zpow_mul"
p2m_open "TateCurve~tsum_succ_prod_eq_tsum_divisors"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Uniqueness

private lemma extraction_step_EP {A Bc : ℕ → K} {ε : ℝ} {q₀ : K} (hq₀0 : q₀ ≠ 0)
    (hq₀1 : ‖q₀‖ < 1) (hq₀ε : ‖q₀‖ < ε)
    (hzero : ∀ q' : K, q' ≠ 0 → ‖q'‖ < ε → HasSum (fun N => (A N - Bc N) * q' ^ N) 0)
    {B₀ : ℝ} (hB₀le : ∀ N, ‖(A N - Bc N) * q₀ ^ N‖ ≤ B₀)
    (N : ℕ) (hlow : ∀ j, j < N → A j - Bc j = 0) :
    A N - Bc N = 0 := by
  have hB₀0 : 0 ≤ B₀ := le_trans (norm_nonneg _) (hB₀le 0)
  have hq₀norm : (0 : ℝ) < ‖q₀‖ := norm_pos_iff.mpr hq₀0

  have hkey : ∀ s : ℕ, ‖A N - Bc N‖ ≤ B₀ * ‖q₀‖ ^ s := by
    intro s
    set t : ℕ := s + N with ht
    set q' : K := q₀ ^ (t + 1) with hq'
    have hq'0 : q' ≠ 0 := pow_ne_zero _ hq₀0
    have hq'norm : ‖q'‖ = ‖q₀‖ ^ (t + 1) := by rw [hq', norm_pow]
    have hq'ε : ‖q'‖ < ε := by
      rw [hq'norm]
      have h1 : ‖q₀‖ ^ (t + 1) ≤ ‖q₀‖ := by
        calc ‖q₀‖ ^ (t + 1) = ‖q₀‖ ^ t * ‖q₀‖ := by rw [pow_succ]
          _ ≤ 1 * ‖q₀‖ := by
              have h2 : ‖q₀‖ ^ t ≤ 1 := pow_le_one₀ (norm_nonneg _) (le_of_lt hq₀1)
              exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
          _ = ‖q₀‖ := one_mul _
      exact lt_of_le_of_lt h1 hq₀ε
    have hH := hzero q' hq'0 hq'ε
    have hsum := hH.summable
    have htsum : ∑' m, (A m - Bc m) * q' ^ m = 0 := hH.tsum_eq

    have hhead : ∑ m ∈ Finset.range (N + 1), (A m - Bc m) * q' ^ m
        = (A N - Bc N) * q' ^ N := by
      refine Finset.sum_eq_single_of_mem N (Finset.mem_range.mpr (by omega)) ?_
      intro j hj hjne
      have hjN : j < N := by
        have := Finset.mem_range.mp hj
        omega
      rw [hlow j hjN, zero_mul]
    have hsplit := hsum.sum_add_tsum_nat_add (N + 1)
    rw [hhead, htsum] at hsplit
    have htail : (A N - Bc N) * q' ^ N
        = -∑' m, (A (m + (N + 1)) - Bc (m + (N + 1))) * q' ^ (m + (N + 1)) := by
      linear_combination hsplit

    have hterm : ∀ m : ℕ,
        ‖(A (m + (N + 1)) - Bc (m + (N + 1))) * q' ^ (m + (N + 1))‖
          ≤ B₀ * ‖q₀‖ ^ (t * (N + 1)) := by
      intro m
      have h1 : ‖(A (m + (N + 1)) - Bc (m + (N + 1))) * q' ^ (m + (N + 1))‖
          = ‖(A (m + (N + 1)) - Bc (m + (N + 1))) * q₀ ^ (m + (N + 1))‖
            * ‖q₀‖ ^ (t * (m + (N + 1))) := by
        rw [norm_mul, norm_mul, hq', norm_pow, norm_pow, norm_pow, ← pow_mul, mul_assoc,
          ← pow_add]
        congr 2
        ring
      rw [h1]
      have h2 : ‖q₀‖ ^ (t * (m + (N + 1))) ≤ ‖q₀‖ ^ (t * (N + 1)) := by
        apply pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt hq₀1)
        have h3 : N + 1 ≤ m + (N + 1) := by omega
        exact Nat.mul_le_mul_left t h3
      calc ‖(A (m + (N + 1)) - Bc (m + (N + 1))) * q₀ ^ (m + (N + 1))‖
            * ‖q₀‖ ^ (t * (m + (N + 1)))
          ≤ B₀ * ‖q₀‖ ^ (t * (m + (N + 1))) :=
            mul_le_mul_of_nonneg_right (hB₀le _) (by positivity)
        _ ≤ B₀ * ‖q₀‖ ^ (t * (N + 1)) := mul_le_mul_of_nonneg_left h2 hB₀0
    have htailnorm : ‖(A N - Bc N) * q' ^ N‖ ≤ B₀ * ‖q₀‖ ^ (t * (N + 1)) := by
      rw [htail, norm_neg]
      exact norm_tsum_le_of_forall_le_of_nonneg (by positivity) hterm

    have hq'powpos : (0 : ℝ) < ‖q'‖ ^ N := pow_pos (norm_pos_iff.mpr hq'0) N
    have hexp : t * (N + 1) = s + (t + 1) * N := by
      rw [ht]; ring
    have hfactor : B₀ * ‖q₀‖ ^ (t * (N + 1)) = (B₀ * ‖q₀‖ ^ s) * ‖q'‖ ^ N := by
      rw [hexp, pow_add, hq'norm, ← pow_mul]
      ring
    have hLHS : ‖(A N - Bc N) * q' ^ N‖ = ‖A N - Bc N‖ * ‖q'‖ ^ N := by
      rw [norm_mul, norm_pow]
    rw [hLHS, hfactor] at htailnorm
    exact le_of_mul_le_mul_right htailnorm hq'powpos

  have hlim : Tendsto (fun s : ℕ => B₀ * ‖q₀‖ ^ s) atTop (nhds 0) := by
    have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q₀) hq₀1
    have h2 := h1.const_mul B₀
    simpa using h2
  have hnorm0 : ‖A N - Bc N‖ ≤ 0 := ge_of_tendsto' hlim hkey
  have hzero' : ‖A N - Bc N‖ = 0 := le_antisymm hnorm0 (norm_nonneg _)
  exact norm_eq_zero.mp hzero'

theorem coeff_eq_of_hasSum_eq {A Bc : ℕ → K} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ q' : K, q' ≠ 0 → ‖q'‖ < ε → ∃ S : K,
      HasSum (fun N => A N * q' ^ N) S ∧ HasSum (fun N => Bc N * q' ^ N) S) :
    ∀ N, A N = Bc N := by

  have hzero : ∀ q' : K, q' ≠ 0 → ‖q'‖ < ε →
      HasSum (fun N => (A N - Bc N) * q' ^ N) 0 := by
    intro q' h0 hlt
    obtain ⟨S, h1, h2⟩ := h q' h0 hlt
    have h3 := h1.sub h2
    rw [sub_self] at h3
    have hfun : (fun N => (A N - Bc N) * q' ^ N)
        = fun N => A N * q' ^ N - Bc N * q' ^ N := by
      funext N; ring
    rwa [hfun]

  obtain ⟨q₀, hq₀pos, hq₀lt⟩ := NormedField.exists_norm_lt K (lt_min hε one_pos)
  have hq₀0 : q₀ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hq₀pos
    exact lt_irrefl _ hq₀pos
  have hq₀ε : ‖q₀‖ < ε := lt_of_lt_of_le hq₀lt (min_le_left _ _)
  have hq₀1 : ‖q₀‖ < 1 := lt_of_lt_of_le hq₀lt (min_le_right _ _)

  have hsum₀ : Summable fun N => (A N - Bc N) * q₀ ^ N := (hzero q₀ hq₀0 hq₀ε).summable
  have htend : Tendsto (fun N => ‖(A N - Bc N) * q₀ ^ N‖) atTop (nhds 0) := by
    have h1 := hsum₀.tendsto_atTop_zero
    have h2 := (continuous_norm.tendsto (0 : K)).comp h1
    simpa [Function.comp_def] using h2
  obtain ⟨B₀, hB₀mem⟩ := htend.bddAbove_range
  have hB₀le : ∀ N, ‖(A N - Bc N) * q₀ ^ N‖ ≤ B₀ := fun N => hB₀mem ⟨N, rfl⟩

  suffices hall : ∀ R N : ℕ, N ≤ R → A N - Bc N = 0 by
    intro N
    exact sub_eq_zero.mp (hall N N le_rfl)
  intro R
  induction R with
  | zero =>
      intro N hNR
      have hN0 : N = 0 := by omega
      subst hN0
      exact extraction_step_EP hq₀0 hq₀1 hq₀ε hzero hB₀le 0 (fun j hj => absurd hj (by omega))
  | succ R ihR =>
      intro N hNR
      rcases Nat.lt_or_ge N (R + 1) with hN | hN
      · exact ihR N (by omega)
      · have hNeq : N = R + 1 := by omega
        subst hNeq
        exact extraction_step_EP hq₀0 hq₀1 hq₀ε hzero hB₀le (R + 1)
          (fun j hj => ihR j (by omega))

end Uniqueness

section Regrouping

variable (c : ℕ → ℕ → K) (q w : K)

private noncomputable def regAlphaTerm_EP (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then c p.1 p.2 * w ^ p.2 * q ^ (p.1 + p.2) else 0

private noncomputable def regAlphaTermT_EP (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 + p.2 ≤ p.1 then c (p.1 - p.2) p.2 * w ^ p.2 * q ^ p.1 else 0

private noncomputable def regBetaTerm_EP (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then c p.1 p.2 * w⁻¹ ^ p.2 * q ^ (p.1 - p.2) else 0

variable {c q w}
variable {B : ℝ}

private def shiftPair_EP : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)

private lemma shiftPair_injective_EP : Function.Injective shiftPair_EP := by
  intro p p' hpp
  obtain ⟨a, b⟩ := p
  obtain ⟨a', b'⟩ := p'
  have hpp' : ((a + b, b) : ℕ × ℕ) = (a' + b', b') := hpp
  injection hpp' with h1 h2
  subst h2
  have h3 : a = a' := by omega
  rw [h3]

private lemma mem_range_shiftPair_EP {p : ℕ × ℕ} (h : p.2 ≤ p.1) : p ∈ Set.range shiftPair_EP := by
  obtain ⟨a, b⟩ := p
  have h' : b ≤ a := h
  refine ⟨(a - b, b), ?_⟩
  show (a - b + b, b) = (a, b)
  have hab : a - b + b = a := by omega
  rw [hab]

private lemma regAlphaTermT_shiftPair_EP (p : ℕ × ℕ) :
    regAlphaTermT_EP c q w (shiftPair_EP p) = regAlphaTerm_EP c q w p := by
  obtain ⟨N, k⟩ := p
  show regAlphaTermT_EP c q w (N + k, k) = regAlphaTerm_EP c q w (N, k)
  rw [regAlphaTermT_EP, regAlphaTerm_EP]
  by_cases hk : 1 ≤ k ∧ k ≤ N
  · rw [if_pos (show 1 ≤ k ∧ k + k ≤ N + k from ⟨hk.1, by omega⟩), if_pos hk,
      Nat.add_sub_cancel]
  · rw [if_neg (fun hcon : 1 ≤ k ∧ k + k ≤ N + k => hk ⟨hcon.1, by omega⟩), if_neg hk]

private lemma inv_pow_mul_pow_of_le_EP (hq0 : q ≠ 0) {k M : ℕ} (hkM : k ≤ M) :
    q⁻¹ ^ k * q ^ M = q ^ (M - k) := by
  have hM : q ^ M = q ^ (M - k) * q ^ k := by
    rw [← pow_add]
    congr 1
    omega
  rw [hM, show q⁻¹ ^ k * (q ^ (M - k) * q ^ k) = q ^ (M - k) * (q⁻¹ ^ k * q ^ k) by ring,
    ← mul_pow, inv_mul_cancel₀ hq0, one_pow, mul_one]

private lemma summable_regAlphaTerm_EP (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    (hq1 : ‖q‖ < 1) (hqw : ‖q‖ * ‖w‖ < 1) : Summable (regAlphaTerm_EP c q w) := by
  have hqw0 : (0 : ℝ) ≤ ‖q‖ * ‖w‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hgeo₁ : Summable fun n : ℕ => ‖q‖ ^ n :=
    summable_geometric_of_lt_one (norm_nonneg q) hq1
  have hgeo₂ : Summable fun k : ℕ => (‖q‖ * ‖w‖) ^ k :=
    summable_geometric_of_lt_one hqw0 hqw
  have hmaj : Summable fun p : ℕ × ℕ => B * (‖q‖ ^ p.1 * (‖q‖ * ‖w‖) ^ p.2) :=
    (hgeo₁.mul_of_nonneg hgeo₂ (fun n => pow_nonneg (norm_nonneg q) n)
      (fun k => pow_nonneg hqw0 k)).mul_left B
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) hmaj)
  by_cases hp : 1 ≤ p.2 ∧ p.2 ≤ p.1
  · rw [regAlphaTerm_EP, if_pos hp]
    calc ‖c p.1 p.2 * w ^ p.2 * q ^ (p.1 + p.2)‖
        = ‖c p.1 p.2‖ * (‖q‖ ^ p.1 * (‖q‖ * ‖w‖) ^ p.2) := by
          rw [norm_mul, norm_mul, norm_pow, norm_pow, pow_add, mul_pow]
          ring
      _ ≤ B * (‖q‖ ^ p.1 * (‖q‖ * ‖w‖) ^ p.2) :=
          mul_le_mul_of_nonneg_right (hc _ _) (by positivity)
  · rw [regAlphaTerm_EP, if_neg hp, norm_zero]
    positivity

private lemma summable_regBetaTerm_comp_EP (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    (hq1 : ‖q‖ < 1) (hw : 1 < ‖w‖) :
    Summable (fun p : ℕ × ℕ => regBetaTerm_EP c q w (shiftPair_EP p)) := by
  have hwinv : ‖w⁻¹‖ < 1 := norm_inv_lt_one_of_one_lt_norm hw
  have hgeo₁ : Summable fun n : ℕ => ‖q‖ ^ n :=
    summable_geometric_of_lt_one (norm_nonneg q) hq1
  have hgeo₂ : Summable fun k : ℕ => ‖w⁻¹‖ ^ k :=
    summable_geometric_of_lt_one (norm_nonneg _) hwinv
  have hmaj : Summable fun p : ℕ × ℕ => B * (‖q‖ ^ p.1 * ‖w⁻¹‖ ^ p.2) :=
    (hgeo₁.mul_of_nonneg hgeo₂ (fun n => pow_nonneg (norm_nonneg q) n)
      (fun k => pow_nonneg (norm_nonneg _) k)).mul_left B
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) hmaj)
  by_cases hp : 1 ≤ p.2
  · rw [show shiftPair_EP p = (p.1 + p.2, p.2) from rfl, regBetaTerm_EP,
      if_pos ⟨hp, Nat.le_add_left _ _⟩, Nat.add_sub_cancel]
    calc ‖c (p.1 + p.2) p.2 * w⁻¹ ^ p.2 * q ^ p.1‖
        = ‖c (p.1 + p.2) p.2‖ * (‖q‖ ^ p.1 * ‖w⁻¹‖ ^ p.2) := by
          rw [norm_mul, norm_mul, norm_pow, norm_pow]
          ring
      _ ≤ B * (‖q‖ ^ p.1 * ‖w⁻¹‖ ^ p.2) :=
          mul_le_mul_of_nonneg_right (hc _ _) (by positivity)
  · rw [show shiftPair_EP p = (p.1 + p.2, p.2) from rfl, regBetaTerm_EP,
      if_neg (fun hcon => hp hcon.1), norm_zero]
    positivity

private lemma hasSum_regAlphaTerm_row_EP (M : ℕ) :
    HasSum (fun k => regAlphaTerm_EP c q w (M, k))
      ((∑ k ∈ Finset.Icc 1 M, c M k * (q * w) ^ k) * q ^ M) := by
  have h0 : ∀ k ∉ Finset.Icc 1 M, regAlphaTerm_EP c q w (M, k) = 0 := by
    intro k hk
    rw [regAlphaTerm_EP, if_neg]
    intro hcon
    exact hk (Finset.mem_Icc.mpr ⟨hcon.1, hcon.2⟩)
  have h1 : HasSum (fun k => regAlphaTerm_EP c q w (M, k))
      (∑ k ∈ Finset.Icc 1 M, regAlphaTerm_EP c q w (M, k)) :=
    hasSum_sum_of_ne_finset_zero h0
  convert h1 using 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_Icc.mp hk
  rw [regAlphaTerm_EP, if_pos ⟨hk'.1, hk'.2⟩, mul_pow, pow_add]
  ring

private lemma hasSum_regBetaTerm_row_EP (hq0 : q ≠ 0) (M : ℕ) :
    HasSum (fun k => regBetaTerm_EP c q w (M, k))
      ((∑ k ∈ Finset.Icc 1 M, c M k * (q * w)⁻¹ ^ k) * q ^ M) := by
  have h0 : ∀ k ∉ Finset.Icc 1 M, regBetaTerm_EP c q w (M, k) = 0 := by
    intro k hk
    rw [regBetaTerm_EP, if_neg]
    intro hcon
    exact hk (Finset.mem_Icc.mpr ⟨hcon.1, hcon.2⟩)
  have h1 : HasSum (fun k => regBetaTerm_EP c q w (M, k))
      (∑ k ∈ Finset.Icc 1 M, regBetaTerm_EP c q w (M, k)) :=
    hasSum_sum_of_ne_finset_zero h0
  convert h1 using 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_Icc.mp hk
  rw [regBetaTerm_EP, if_pos ⟨hk'.1, hk'.2⟩, mul_inv_rev, mul_pow,
    show c M k * (w⁻¹ ^ k * q⁻¹ ^ k) * q ^ M = c M k * w⁻¹ ^ k * (q⁻¹ ^ k * q ^ M) by ring,
    inv_pow_mul_pow_of_le_EP hq0 hk'.2]

private lemma specAlpha_eq_sum_Icc_EP (M : ℕ) :
    specAlpha c w M
      = ∑ k ∈ Finset.Icc 1 M, (if k + k ≤ M then c (M - k) k * w ^ k else 0) := by
  have himage : (Finset.HasAntidiagonal.antidiagonal M).filter (fun p => 1 ≤ p.2 ∧ p.2 ≤ p.1)
      = ((Finset.Icc 1 M).filter (fun k => k + k ≤ M)).image (fun k => (M - k, k)) := by
    ext p
    simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨hsum, h1, h2⟩
      refine ⟨p.2, ⟨⟨h1, by omega⟩, by omega⟩, ?_⟩
      obtain ⟨a, b⟩ := p
      simp only at hsum h1 h2 ⊢
      exact Prod.ext (by omega) rfl
    · rintro ⟨k, ⟨⟨hk1, hkM⟩, hkk⟩, rfl⟩
      exact ⟨by omega, hk1, by omega⟩
  calc specAlpha c w M
      = ∑ p ∈ ((Finset.Icc 1 M).filter (fun k => k + k ≤ M)).image (fun k => (M - k, k)),
          c p.1 p.2 * w ^ p.2 := by rw [specAlpha, himage]
    _ = ∑ k ∈ (Finset.Icc 1 M).filter (fun k => k + k ≤ M), c (M - k) k * w ^ k :=
        Finset.sum_image (fun k₁ _ k₂ _ h => congrArg Prod.snd h)
    _ = ∑ k ∈ Finset.Icc 1 M, (if k + k ≤ M then c (M - k) k * w ^ k else 0) :=
        Finset.sum_filter _ _

private lemma hasSum_regAlphaTermT_fiber_EP (T : ℕ) :
    HasSum (fun k => regAlphaTermT_EP c q w (T, k)) (specAlpha c w T * q ^ T) := by
  have h0 : ∀ k ∉ Finset.Icc 1 T, regAlphaTermT_EP c q w (T, k) = 0 := by
    intro k hk
    rw [regAlphaTermT_EP, if_neg]
    intro hcon
    exact hk (Finset.mem_Icc.mpr ⟨hcon.1, by omega⟩)
  have h1 : HasSum (fun k => regAlphaTermT_EP c q w (T, k))
      (∑ k ∈ Finset.Icc 1 T, regAlphaTermT_EP c q w (T, k)) :=
    hasSum_sum_of_ne_finset_zero h0
  convert h1 using 1
  rw [specAlpha_eq_sum_Icc_EP, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hcond : k + k ≤ T
  · rw [if_pos hcond, regAlphaTermT_EP,
      if_pos ⟨(Finset.mem_Icc.mp hk).1, by simpa using hcond⟩]
  · rw [if_neg hcond, regAlphaTermT_EP, if_neg, zero_mul]
    intro hcon
    exact hcond (by simpa using hcon.2)

private lemma hasSum_regBetaTerm_tail_EP (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    (hw : 1 < ‖w‖) (T : ℕ) :
    HasSum (fun k => regBetaTerm_EP c q w (shiftPair_EP (T, k))) (specTail c w T * q ^ T) := by
  have h1 : (fun k => regBetaTerm_EP c q w (shiftPair_EP (T, k)))
      = fun k => (if 1 ≤ k then c (T + k) k * w⁻¹ ^ k else 0) * q ^ T := by
    funext k
    by_cases hk : 1 ≤ k
    · rw [show shiftPair_EP (T, k) = (T + k, k) from rfl, regBetaTerm_EP,
        if_pos ⟨hk, Nat.le_add_left k T⟩, if_pos hk, Nat.add_sub_cancel]
    · rw [show shiftPair_EP (T, k) = (T + k, k) from rfl, regBetaTerm_EP,
        if_neg (fun hcon => hk hcon.1), if_neg hk, zero_mul]
  rw [h1]
  have h2 : HasSum (fun k : ℕ => if 1 ≤ k then c (T + k) k * w⁻¹ ^ k else 0)
      (specTail c w T) := by
    have h3 := (summable_specTail_term hB hc hw T).hasSum
    rwa [show specTail c w T
      = ∑' k : ℕ, if 1 ≤ k then c (T + k) k * w⁻¹ ^ k else 0 from rfl]
  exact h2.mul_right (q ^ T)

theorem hasSum_masterShape_of_hasSum_shifted (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) {S : K}
    (h : HasSum (fun M =>
      (∑ k ∈ Finset.Icc 1 M, c M k * ((q * w) ^ k + (q * w)⁻¹ ^ k - 2)) * q ^ M) S) :
    HasSum (fun M => (specAlpha c w M + specTail c w M + specGamma c M) * q ^ M) S := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hw hqw

  have hsummA : Summable (regAlphaTerm_EP c q w) := summable_regAlphaTerm_EP hB hc hq1 hqw
  set Sα : K := ∑' p : ℕ × ℕ, regAlphaTerm_EP c q w p with hSα
  have hA : HasSum (regAlphaTerm_EP c q w) Sα := hsummA.hasSum
  have hA1 : HasSum (fun M => (∑ k ∈ Finset.Icc 1 M, c M k * (q * w) ^ k) * q ^ M) Sα :=
    hA.prod_fiberwise (fun M => hasSum_regAlphaTerm_row_EP M)
  have hAcomp : HasSum (fun p : ℕ × ℕ => regAlphaTermT_EP c q w (shiftPair_EP p)) Sα := by
    have hfun : (fun p : ℕ × ℕ => regAlphaTermT_EP c q w (shiftPair_EP p)) = regAlphaTerm_EP c q w := by
      funext p
      exact regAlphaTermT_shiftPair_EP p
    rwa [hfun]
  have hAvan : ∀ p ∉ Set.range shiftPair_EP, regAlphaTermT_EP c q w p = 0 := by
    intro p hp
    rw [regAlphaTermT_EP, if_neg]
    intro hcon
    exact hp (mem_range_shiftPair_EP (by omega))
  have hAT : HasSum (regAlphaTermT_EP c q w) Sα :=
    (shiftPair_injective_EP.hasSum_iff hAvan).mp hAcomp
  have hA2 : HasSum (fun T => specAlpha c w T * q ^ T) Sα :=
    hAT.prod_fiberwise (fun T => hasSum_regAlphaTermT_fiber_EP T)

  have hsummBc : Summable (fun p : ℕ × ℕ => regBetaTerm_EP c q w (shiftPair_EP p)) :=
    summable_regBetaTerm_comp_EP hB hc hq1 hw
  set Sβ : K := ∑' p : ℕ × ℕ, regBetaTerm_EP c q w (shiftPair_EP p) with hSβ
  have hBe : HasSum (fun p : ℕ × ℕ => regBetaTerm_EP c q w (shiftPair_EP p)) Sβ := hsummBc.hasSum
  have hBvan : ∀ p ∉ Set.range shiftPair_EP, regBetaTerm_EP c q w p = 0 := by
    intro p hp
    rw [regBetaTerm_EP, if_neg]
    intro hcon
    exact hp (mem_range_shiftPair_EP hcon.2)
  have hB' : HasSum (regBetaTerm_EP c q w) Sβ := (shiftPair_injective_EP.hasSum_iff hBvan).mp hBe
  have hB1 : HasSum (fun M => (∑ k ∈ Finset.Icc 1 M, c M k * (q * w)⁻¹ ^ k) * q ^ M) Sβ :=
    hB'.prod_fiberwise (fun M => hasSum_regBetaTerm_row_EP hq0 M)
  have hB2 : HasSum (fun T => specTail c w T * q ^ T) Sβ :=
    hBe.prod_fiberwise (fun T => hasSum_regBetaTerm_tail_EP hB hc hw T)

  have hsplit : (fun M =>
      (∑ k ∈ Finset.Icc 1 M, c M k * ((q * w) ^ k + (q * w)⁻¹ ^ k - 2)) * q ^ M)
      = fun M => ((∑ k ∈ Finset.Icc 1 M, c M k * (q * w) ^ k) * q ^ M)
          + ((∑ k ∈ Finset.Icc 1 M, c M k * (q * w)⁻¹ ^ k) * q ^ M)
          + ((∑ k ∈ Finset.Icc 1 M, c M k * (-2 : K)) * q ^ M) := by
    funext M
    rw [show (∑ k ∈ Finset.Icc 1 M, c M k * ((q * w) ^ k + (q * w)⁻¹ ^ k - 2))
        = (∑ k ∈ Finset.Icc 1 M, c M k * (q * w) ^ k)
          + (∑ k ∈ Finset.Icc 1 M, c M k * (q * w)⁻¹ ^ k)
          + (∑ k ∈ Finset.Icc 1 M, c M k * (-2 : K)) by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring]
    ring
  rw [hsplit] at h

  have hG : HasSum (fun M => (∑ k ∈ Finset.Icc 1 M, c M k * (-2 : K)) * q ^ M)
      (S - Sα - Sβ) := by
    have h1 := (h.sub hA1).sub hB1
    have h2 : (fun M =>
        (((∑ k ∈ Finset.Icc 1 M, c M k * (q * w) ^ k) * q ^ M)
          + ((∑ k ∈ Finset.Icc 1 M, c M k * (q * w)⁻¹ ^ k) * q ^ M)
          + ((∑ k ∈ Finset.Icc 1 M, c M k * (-2 : K)) * q ^ M)
          - (∑ k ∈ Finset.Icc 1 M, c M k * (q * w) ^ k) * q ^ M)
          - (∑ k ∈ Finset.Icc 1 M, c M k * (q * w)⁻¹ ^ k) * q ^ M)
        = fun M => (∑ k ∈ Finset.Icc 1 M, c M k * (-2 : K)) * q ^ M := by
      funext M
      ring
    rwa [h2] at h1

  have hG' : HasSum (fun M => specGamma c M * q ^ M) (S - Sα - Sβ) := by
    have h2 : (fun M => (∑ k ∈ Finset.Icc 1 M, c M k * (-2 : K)) * q ^ M)
        = fun M => specGamma c M * q ^ M := by
      funext M
      congr 1
      rw [show specGamma c M = ∑ k ∈ Finset.Icc 1 M, (-2 : K) * c M k from rfl]
      exact Finset.sum_congr rfl fun k _ => by ring
    rwa [h2] at hG

  have hfinal := (hA2.add hB2).add hG'
  have hval : Sα + Sβ + (S - Sα - Sβ) = S := by ring
  rw [hval] at hfinal
  have hfun : (fun M => (specAlpha c w M * q ^ M + specTail c w M * q ^ M)
      + specGamma c M * q ^ M)
      = fun M => (specAlpha c w M + specTail c w M + specGamma c M) * q ^ M := by
    funext M
    ring
  rwa [hfun] at hfinal

end Regrouping

section MasterFromRepresentation

variable {B : ℝ} {c : ℕ → ℕ → K} {w : K}

theorem master_of_qshift_representation (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    {D : K → K} (hw : 1 < ‖w‖)
    (hrepr : ∀ q' : K, q' ≠ 0 → ‖q'‖ * ‖w‖ < 1 →
      HasSum (fun M =>
        (∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2)) * q' ^ M) (D q')
      ∧ HasSum (fun M =>
        (∑ k ∈ Finset.Icc 1 M, c M k * ((q' * w) ^ k + (q' * w)⁻¹ ^ k - 2)) * q' ^ M) (D q')) :
    ∀ M : ℕ, ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2)
      = specAlpha c w M + specTail c w M + specGamma c M := by
  have hw0 : (0 : ℝ) < ‖w‖ := lt_trans one_pos hw
  have hε : (0 : ℝ) < ‖w‖⁻¹ := by positivity
  refine coeff_eq_of_hasSum_eq hε (fun q' hq'0 hq'lt => ?_)
  have hq'w : ‖q'‖ * ‖w‖ < 1 := by
    calc ‖q'‖ * ‖w‖ < ‖w‖⁻¹ * ‖w‖ := mul_lt_mul_of_pos_right hq'lt hw0
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hw0)
  obtain ⟨h1, h2⟩ := hrepr q' hq'0 hq'w
  exact ⟨D q', h1, hasSum_masterShape_of_hasSum_shifted hB hc hq'0 hw hq'w h2⟩

end MasterFromRepresentation

section ProductDefect

variable {q u v : K}

theorem symAdd_prod_of_qExpansion (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    {B : ℝ} (hB : 0 ≤ B) {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B)
    (hrepr : ∀ q' u' v' : K, q' ≠ 0 → ‖q'‖ < 1 → AddParams q' u' v' →
      ‖q'‖ < ‖u'‖ → ‖u'‖ < ‖q'‖⁻¹ → ‖q'‖ < ‖v'‖ → ‖v'‖ < ‖q'‖⁻¹ →
      ‖q'‖ < ‖u' * v'‖ → ‖u' * v'‖ < ‖q'‖⁻¹ → ‖q'‖ < ‖u' * v'⁻¹‖ → ‖u' * v'⁻¹‖ < ‖q'‖⁻¹ →
      HasSum (fun M => (∑ k ∈ Finset.Icc 1 M,
          (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k + u'⁻¹ ^ k - 2)) * q' ^ M)
        (addDefectProd q' u' v'))
    (hP : AddParams q u v)
    (hu_lo : ‖q‖ < ‖u‖) (hu_hi : ‖u‖ < ‖q‖⁻¹) (hv_lo : ‖q‖ < ‖v‖) (hv_hi : ‖v‖ < ‖q‖⁻¹)
    (huv_lo : ‖q‖ < ‖u * v‖) (huv_hi : ‖u * v‖ < ‖q‖⁻¹)
    (huvi_lo : ‖q‖ < ‖u * v⁻¹‖) (huvi_hi : ‖u * v⁻¹‖ < ‖q‖⁻¹) :
    pointX q (u * v) * pointX q (u * v⁻¹) * (pointX q u - pointX q v) ^ 2 =
      symProdNum q (pointX q u) (pointX q v) := by
  refine symAdd_prod_of_laurentRows hq0 hq1 hB ha ?_ hP.v_ne_zero
    (hrepr q u v hq0 hq1 hP hu_lo hu_hi hv_lo hv_hi huv_lo huv_hi huvi_lo huvi_hi)

  intro n M w hw
  have hvS1 : ‖unitSpectator q n‖ = 1 := norm_unitSpectator hq0 hq1 n
  have hvSne1 : unitSpectator q n ≠ 1 := unitSpectator_ne_one hq0 n
  refine (master_of_qshift_representation
    (D := fun q' => addDefectProd q' w (unitSpectator q n)) hB
    (fun N k => norm_spectatorRows_le hB ha hvS1 N k) hw ?_) M
  intro q' hq'0 hq'w
  have hq'1 : ‖q'‖ < 1 := norm_q_lt_one_of_qshift hw hq'w
  have hq'pos : (0 : ℝ) < ‖q'‖ := norm_pos_iff.mpr hq'0
  have hq'inv1 : 1 < ‖q'‖⁻¹ := one_lt_inv_iff₀.mpr ⟨hq'pos, hq'1⟩

  have hPn : AddParams q' w (unitSpectator q n) :=
    addParams_of_norm_one_spectator hq'0 hw hq'w hvS1 hvSne1
  have hwv : ‖w * unitSpectator q n‖ = ‖w‖ := norm_mul_eq_of_norm_eq_one hvS1 w
  have hwvi : ‖w * (unitSpectator q n)⁻¹‖ = ‖w‖ := norm_mul_inv_eq_of_norm_eq_one hvS1 w
  have hw_lo : ‖q'‖ < ‖w‖ := lt_trans hq'1 hw
  have hw_hi : ‖w‖ < ‖q'‖⁻¹ := by
    rw [← one_div, lt_div_iff₀ hq'pos]
    calc ‖w‖ * ‖q'‖ = ‖q'‖ * ‖w‖ := mul_comm _ _
      _ < 1 := hq'w
  constructor
  ·
    have h1 := hrepr q' w (unitSpectator q n) hq'0 hq'1 hPn hw_lo hw_hi
      (by rw [hvS1]; exact hq'1) (by rw [hvS1]; exact hq'inv1)
      (by rw [hwv]; exact hw_lo) (by rw [hwv]; exact hw_hi)
      (by rw [hwvi]; exact hw_lo) (by rw [hwvi]; exact hw_hi)
    simpa only [spectatorRows] using h1
  ·
    have hP2 : AddParams q' (q' * w) (unitSpectator q n) := hPn.q_mul_left
    have hq'wnorm : ‖q' * w‖ = ‖q'‖ * ‖w‖ := norm_mul _ _
    have h2lo : ‖q'‖ < ‖q' * w‖ := by
      rw [hq'wnorm]
      exact (lt_mul_iff_one_lt_right hq'pos).mpr hw
    have h2hi : ‖q' * w‖ < ‖q'‖⁻¹ := by
      rw [hq'wnorm]
      exact lt_trans hq'w hq'inv1
    have h2uv : ‖q' * w * unitSpectator q n‖ = ‖q' * w‖ :=
      norm_mul_eq_of_norm_eq_one hvS1 _
    have h2uvi : ‖q' * w * (unitSpectator q n)⁻¹‖ = ‖q' * w‖ :=
      norm_mul_inv_eq_of_norm_eq_one hvS1 _
    have h2 := hrepr q' (q' * w) (unitSpectator q n) hq'0 hq'1 hP2 h2lo h2hi
      (by rw [hvS1]; exact hq'1) (by rw [hvS1]; exact hq'inv1)
      (by rw [h2uv]; exact h2lo) (by rw [h2uv]; exact h2hi)
      (by rw [h2uvi]; exact h2lo) (by rw [h2uvi]; exact h2hi)
    rw [addDefectProd_q_mul_left hq'0] at h2
    simpa only [spectatorRows] using h2

end ProductDefect

end TateCurve

set_option autoImplicit false

set_option linter.unusedSectionVars false

open scoped NNReal
open IsUltrametricDist Filter Finset

namespace TateCurve
p2m_export "TateCurve" "eq_zero_of_master_rows unitSpectator norm_unitSpectator unitSpectator_ne_one spectatorRows norm_spectatorRows_le symAdd_sum_of_laurentRows symAdd_prod_of_laurentRows symSumNum symProdNum OffLattice OffLattice.zpow_mul OffLattice.inv AddParams AddParams.swap pointX_inv_mul pointX_inv_mul_inv pointX_q_inv_mul addDefectSum addDefectProd addDefectSum_q_mul_left addDefectProd_q_mul_left nodal_symSum offLattice_of_norm_eq_one addParams_of_norm_one_spectator norm_mul_eq_of_norm_eq_one norm_mul_inv_eq_of_norm_eq_one specTail specAlpha specGamma summable_specTail_term norm_specTail_le spec_eq_zero_of_master summable_norm_a₄Series summable_norm_a₆Series summable_norm_xSeries summable_norm_ySeries ne_zero_of_one_lt_norm norm_q_lt_one_of_qshift norm_inv_lt_one_of_one_lt_norm cauchyMul_two tent xfun_mul_Fz_eq_tent cauchyMul cauchyMul_zero cauchyMul_one qSeries_mul summable_norm_cauchyMul xCoeffFull xCoeffFull_zero xCoeffFull_succ yCoeffFull yCoeffFull_zero yCoeffFull_succ a₄Coeff a₄Coeff_zero a₄Coeff_succ a₆Coeff a₆Coeff_zero a₆Coeff_succ xfun yfun pointX pointY term term_zero summable_term coeffSum b a₄ a₆ curve curve_a₁ curve_a₃ xDivTerm yDivTerm xCoeff yCoeff pointX_inv pointX_q_mul pointX_zpow_mul pointPsiTwo addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff psiCoeffFull addDefectDiffCoeff LatticeRep OnHalfLattice MuTranslation pointX_qExpansion pointY_qExpansion pointY_q_mul pointY_inv pointY_zpow_mul"
p2m_open "TateCurve~tsum_succ_prod_eq_tsum_divisors"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Uniqueness

set_option maxHeartbeats 4000000 in

private lemma rowCoeff_eq_zero_step_ES {c : ℕ → K} {q₀ : K} (hq₀0 : q₀ ≠ 0) (hq₀1 : ‖q₀‖ < 1)
    {B : ℝ} (hBle : ∀ N, ‖c N * q₀ ^ N‖ ≤ B)
    (hcsum : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖q₀‖ → Summable fun N => c N * q ^ N)
    (hczero : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖q₀‖ → ∑' N, c N * q ^ N = 0)
    (N₀ : ℕ) (hlow : ∀ j, j < N₀ → c j = 0) : c N₀ = 0 := by
  have hq₀norm : 0 < ‖q₀‖ := norm_pos_iff.mpr hq₀0
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hBle 0)
  have hC0 : (0 : ℝ) ≤ B / ‖q₀‖ ^ (N₀ + 1) :=
    div_nonneg hB0 (le_of_lt (pow_pos hq₀norm _))

  have hA : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖q₀‖ → ‖c N₀‖ ≤ B / ‖q₀‖ ^ (N₀ + 1) * ‖q‖ := by
    intro q hq hqle
    have hqnorm : 0 < ‖q‖ := norm_pos_iff.mpr hq
    have hsum := hcsum q hq hqle
    have hsplit1 : (∑ i ∈ Finset.range N₀, c i * q ^ i) + ∑' i, c (i + N₀) * q ^ (i + N₀)
        = ∑' i, c i * q ^ i := hsum.sum_add_tsum_nat_add N₀
    have hhead : (∑ i ∈ Finset.range N₀, c i * q ^ i) = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hlow i (Finset.mem_range.mp hi), zero_mul]
    have hshift : Summable fun i => c (i + N₀) * q ^ (i + N₀) :=
      (summable_nat_add_iff N₀).mpr hsum
    have htail0 : ∑' i, c (i + N₀) * q ^ (i + N₀) = 0 := by
      have h0 := hczero q hq hqle
      rw [← hsplit1, hhead, zero_add] at h0
      exact h0
    have hsplit2 : ∑' i, c (i + N₀) * q ^ (i + N₀)
        = c N₀ * q ^ N₀ + ∑' i, c (i + 1 + N₀) * q ^ (i + 1 + N₀) := by
      rw [hshift.tsum_eq_zero_add]
      simp only [Nat.zero_add]
    have hkey : c N₀ * q ^ N₀ = - ∑' i, c (i + 1 + N₀) * q ^ (i + 1 + N₀) := by
      have h0 := htail0
      rw [hsplit2] at h0
      exact eq_neg_of_add_eq_zero_left h0
    have hratio0 : 0 ≤ ‖q‖ / ‖q₀‖ := div_nonneg (norm_nonneg _) (norm_nonneg _)
    have hratio_le_one : ‖q‖ / ‖q₀‖ ≤ 1 := (div_le_one hq₀norm).mpr hqle
    have htermbound : ∀ i, ‖c (i + 1 + N₀) * q ^ (i + 1 + N₀)‖
        ≤ B / ‖q₀‖ ^ (N₀ + 1) * ‖q‖ ^ (N₀ + 1) := by
      intro i
      have hq₀j : (0 : ℝ) < ‖q₀‖ ^ (i + 1 + N₀) := pow_pos hq₀norm _
      have h1 : ‖c (i + 1 + N₀) * q ^ (i + 1 + N₀)‖
          = ‖c (i + 1 + N₀) * q₀ ^ (i + 1 + N₀)‖ * (‖q‖ / ‖q₀‖) ^ (i + 1 + N₀) := by
        rw [norm_mul, norm_mul, norm_pow, norm_pow, div_pow]
        field_simp
      have h2 : (‖q‖ / ‖q₀‖) ^ (i + 1 + N₀) ≤ (‖q‖ / ‖q₀‖) ^ (N₀ + 1) := by
        have hsplit : (‖q‖ / ‖q₀‖) ^ (i + 1 + N₀)
            = (‖q‖ / ‖q₀‖) ^ (N₀ + 1) * (‖q‖ / ‖q₀‖) ^ ((i + 1 + N₀) - (N₀ + 1)) := by
          rw [← pow_add]
          congr 1
          omega
        rw [hsplit]
        have h3 : (‖q‖ / ‖q₀‖) ^ ((i + 1 + N₀) - (N₀ + 1)) ≤ 1 :=
          pow_le_one₀ hratio0 hratio_le_one
        have h4 : (0 : ℝ) ≤ (‖q‖ / ‖q₀‖) ^ (N₀ + 1) := pow_nonneg hratio0 _
        nlinarith
      have h5 : B / ‖q₀‖ ^ (N₀ + 1) * ‖q‖ ^ (N₀ + 1) = B * (‖q‖ / ‖q₀‖) ^ (N₀ + 1) := by
        rw [div_pow]
        field_simp
      calc ‖c (i + 1 + N₀) * q ^ (i + 1 + N₀)‖
          = ‖c (i + 1 + N₀) * q₀ ^ (i + 1 + N₀)‖ * (‖q‖ / ‖q₀‖) ^ (i + 1 + N₀) := h1
        _ ≤ B * (‖q‖ / ‖q₀‖) ^ (N₀ + 1) := by
            have h6 := hBle (i + 1 + N₀)
            have h7 : (0 : ℝ) ≤ (‖q‖ / ‖q₀‖) ^ (i + 1 + N₀) := pow_nonneg hratio0 _
            nlinarith [norm_nonneg (c (i + 1 + N₀) * q₀ ^ (i + 1 + N₀))]
        _ = B / ‖q₀‖ ^ (N₀ + 1) * ‖q‖ ^ (N₀ + 1) := h5.symm
    have htail_le : ‖∑' i, c (i + 1 + N₀) * q ^ (i + 1 + N₀)‖
        ≤ B / ‖q₀‖ ^ (N₀ + 1) * ‖q‖ ^ (N₀ + 1) :=
      norm_tsum_le_of_forall_le_of_nonneg
        (mul_nonneg hC0 (pow_nonneg (norm_nonneg _) _)) htermbound
    have h8 : ‖c N₀‖ * ‖q‖ ^ N₀ ≤ (B / ‖q₀‖ ^ (N₀ + 1) * ‖q‖) * ‖q‖ ^ N₀ := by
      have h9 : ‖c N₀ * q ^ N₀‖ ≤ B / ‖q₀‖ ^ (N₀ + 1) * ‖q‖ ^ (N₀ + 1) := by
        rw [hkey, norm_neg]
        exact htail_le
      rw [norm_mul, norm_pow] at h9
      calc ‖c N₀‖ * ‖q‖ ^ N₀ ≤ B / ‖q₀‖ ^ (N₀ + 1) * ‖q‖ ^ (N₀ + 1) := h9
        _ = (B / ‖q₀‖ ^ (N₀ + 1) * ‖q‖) * ‖q‖ ^ N₀ := by rw [pow_succ]; ring
    exact le_of_mul_le_mul_right h8 (pow_pos hqnorm N₀)

  have hbound : ∀ t : ℕ, ‖c N₀‖ ≤ B / ‖q₀‖ ^ (N₀ + 1) * ‖q₀‖ ^ (t + 1) := by
    intro t
    have hqt0 : q₀ ^ (t + 1) ≠ 0 := pow_ne_zero _ hq₀0
    have hqtle : ‖q₀ ^ (t + 1)‖ ≤ ‖q₀‖ := by
      rw [norm_pow]
      have h1 : ‖q₀‖ ^ t ≤ 1 := pow_le_one₀ (norm_nonneg q₀) (le_of_lt hq₀1)
      calc ‖q₀‖ ^ (t + 1) = ‖q₀‖ ^ t * ‖q₀‖ := by rw [pow_succ]
        _ ≤ 1 * ‖q₀‖ := by nlinarith [norm_nonneg q₀]
        _ = ‖q₀‖ := one_mul _
    have h2 := hA (q₀ ^ (t + 1)) hqt0 hqtle
    rwa [norm_pow] at h2
  have hgeo : Tendsto (fun t : ℕ => B / ‖q₀‖ ^ (N₀ + 1) * ‖q₀‖ ^ (t + 1)) atTop (nhds 0) := by
    have h1 : Tendsto (fun t : ℕ => ‖q₀‖ ^ t) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hq₀1
    have h2 : Tendsto (fun t : ℕ => ‖q₀‖ ^ (t + 1)) atTop (nhds 0) :=
      h1.comp (tendsto_add_atTop_nat 1)
    have h3 := h2.const_mul (B / ‖q₀‖ ^ (N₀ + 1))
    simpa using h3
  have hzero : Tendsto (fun _ : ℕ => c N₀) atTop (nhds 0) := squeeze_zero_norm hbound hgeo
  exact tendsto_nhds_unique tendsto_const_nhds hzero

set_option maxHeartbeats 4000000 in

private lemma rowCoeff_eq_of_forall_tsum_eq_ES {a b : ℕ → K} {q₀ : K} (hq₀0 : q₀ ≠ 0)
    (hq₀1 : ‖q₀‖ < 1)
    (ha : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖q₀‖ → Summable fun N => a N * q ^ N)
    (hb : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖q₀‖ → Summable fun N => b N * q ^ N)
    (heq : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖q₀‖ → ∑' N, a N * q ^ N = ∑' N, b N * q ^ N) :
    ∀ N, a N = b N := by
  have hcsum : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖q₀‖ → Summable fun N => (a N - b N) * q ^ N := by
    intro q hq hqle
    exact ((ha q hq hqle).sub (hb q hq hqle)).congr fun N => by ring
  have hczero : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖q₀‖ → ∑' N, (a N - b N) * q ^ N = 0 := by
    intro q hq hqle
    have h1 : ∑' N, (a N - b N) * q ^ N = (∑' N, a N * q ^ N) - ∑' N, b N * q ^ N := by
      rw [← (ha q hq hqle).tsum_sub (hb q hq hqle)]
      exact tsum_congr fun N => by ring
    rw [h1, heq q hq hqle, sub_self]
  have hterms : Tendsto (fun N => ‖(a N - b N) * q₀ ^ N‖) atTop (nhds 0) := by
    have h1 := (hcsum q₀ hq₀0 le_rfl).tendsto_atTop_zero
    have h2 := (continuous_norm.tendsto (0 : K)).comp h1
    simpa [Function.comp_def] using h2
  obtain ⟨B, hBmem⟩ := hterms.bddAbove_range
  have hBle : ∀ N, ‖(a N - b N) * q₀ ^ N‖ ≤ B := fun N => hBmem ⟨N, rfl⟩
  have hall : ∀ Bnd N, N ≤ Bnd → a N - b N = 0 := by
    intro Bnd
    induction Bnd with
    | zero =>
        intro N hN
        have hN0 : N = 0 := by omega
        subst hN0
        exact rowCoeff_eq_zero_step_ES hq₀0 hq₀1 hBle hcsum hczero 0
          fun j hj => absurd hj (by omega)
    | succ Bnd ihB =>
        intro N hN
        rcases Nat.lt_or_ge N (Bnd + 1) with h | h
        · exact ihB N (by omega)
        · have hNeq : N = Bnd + 1 := by omega
          subst hNeq
          exact rowCoeff_eq_zero_step_ES hq₀0 hq₀1 hBle hcsum hczero (Bnd + 1)
            fun j hj => ihB j (by omega)
  intro N
  exact sub_eq_zero.mp (hall N N le_rfl)

end Uniqueness

section Reindex

private def shiftPair_ES : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)

private lemma shiftPair_injective_ES : Function.Injective shiftPair_ES := by
  intro p p' h
  obtain ⟨a, b⟩ := p
  obtain ⟨a', b'⟩ := p'
  simp only [shiftPair_ES, Prod.mk.injEq] at h ⊢
  omega

private lemma mem_range_shiftPair_ES {p : ℕ × ℕ} (h : p.2 ≤ p.1) : p ∈ Set.range shiftPair_ES :=
  ⟨(p.1 - p.2, p.2), by
    simp only [shiftPair_ES]
    exact Prod.ext (by omega) rfl⟩

private lemma tsum_prod_eq_tsum_sum_antidiagonal_ES {f : ℕ × ℕ → K} (hf : Summable f) :
    ∑' p : ℕ × ℕ, f p = ∑' M : ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal M, f p := by
  have he := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq f
  rw [← he]
  have hsum : Summable fun x : Σ M : ℕ, (Finset.HasAntidiagonal.antidiagonal M : Finset (ℕ × ℕ)) =>
      f (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd x) := by
    have h1 := (Equiv.summable_iff (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ))).mpr hf
    simpa [Function.comp_def] using h1
  rw [hsum.tsum_sigma]
  refine tsum_congr fun M => ?_
  rw [tsum_fintype, ← Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal M) f]
  exact Finset.sum_congr rfl fun c _ => rfl

end Reindex

section Families

variable (c : ℕ → ℕ → K) (w q : K)

private noncomputable def hubT_ES (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then
    c p.1 p.2 * ((q * w) ^ p.2 + (q * w)⁻¹ ^ p.2 - 2) * q ^ p.1 else 0

private noncomputable def alphaT_ES (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then c p.1 p.2 * w ^ p.2 * q ^ (p.1 + p.2) else 0

private noncomputable def betaT_ES (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then c p.1 p.2 * w⁻¹ ^ p.2 * q ^ (p.1 - p.2) else 0

private noncomputable def gammaT_ES (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then (-2 : K) * c p.1 p.2 * q ^ p.1 else 0

variable {c w q}

private lemma hubT_eq_ES (hq0 : q ≠ 0) (_hw0 : w ≠ 0) (p : ℕ × ℕ) :
    hubT_ES c w q p = alphaT_ES c w q p + betaT_ES c w q p + gammaT_ES c q p := by
  simp only [hubT_ES, alphaT_ES, betaT_ES, gammaT_ES]
  by_cases hg : 1 ≤ p.2 ∧ p.2 ≤ p.1
  · rw [if_pos hg, if_pos hg, if_pos hg, if_pos hg]
    obtain ⟨j, hj⟩ : ∃ j, p.1 = j + p.2 := ⟨p.1 - p.2, by omega⟩
    rw [hj]
    have hsub : j + p.2 - p.2 = j := by omega
    rw [hsub]
    have hqp : q ^ p.2 ≠ 0 := pow_ne_zero _ hq0
    have hcancel : q ^ p.2 * q⁻¹ ^ p.2 = 1 := by
      rw [inv_pow, mul_inv_cancel₀ hqp]
    have hsplit : (q * w)⁻¹ ^ p.2 = q⁻¹ ^ p.2 * w⁻¹ ^ p.2 := by
      rw [mul_inv, mul_pow]
    rw [hsplit]
    linear_combination (c (j + p.2) p.2 * w⁻¹ ^ p.2 * q ^ j) * hcancel
  · rw [if_neg hg, if_neg hg, if_neg hg, if_neg hg]
    ring

private lemma summable_of_shift_bound_ES {f : ℕ × ℕ → K} {C s ρ : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hvanish : ∀ p : ℕ × ℕ, ¬ p.2 ≤ p.1 → f p = 0)
    (hbound : ∀ p : ℕ × ℕ, ‖f (shiftPair_ES p)‖ ≤ C * (s ^ p.1 * ρ ^ p.2)) :
    Summable f := by
  have hgeom : Summable fun p : ℕ × ℕ => C * (s ^ p.1 * ρ ^ p.2) :=
    ((summable_geometric_of_lt_one hs0 hs1).mul_of_nonneg
      (summable_geometric_of_lt_one hρ0 hρ1)
      (fun _ => pow_nonneg hs0 _) (fun _ => pow_nonneg hρ0 _)).mul_left C
  have hcomp : Summable fun p : ℕ × ℕ => f (shiftPair_ES p) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _) hbound hgeom)
  have hsupport : ∀ x ∉ Set.range shiftPair_ES, f x = 0 := by
    intro x hx
    refine hvanish x fun hle => hx (mem_range_shiftPair_ES hle)
  have hcomp' : Summable (f ∘ shiftPair_ES) := by exact hcomp
  exact (shiftPair_injective_ES.summable_iff hsupport).mp hcomp'

variable {B : ℝ}

set_option maxHeartbeats 4000000 in
private lemma summable_alphaT_ES (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) : Summable (alphaT_ES c w q) := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hw hqw
  refine summable_of_shift_bound_ES (C := B) (norm_nonneg q) hq1
    (mul_nonneg (norm_nonneg q) (norm_nonneg w)) hqw ?_ ?_
  · intro p hp
    simp only [alphaT_ES]
    exact if_neg fun hg => hp hg.2
  · intro p
    simp only [alphaT_ES, shiftPair_ES]
    by_cases hg : 1 ≤ p.2
    · rw [if_pos ⟨hg, by omega⟩]
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      have h1 : ‖c (p.1 + p.2) p.2‖ ≤ B := hc _ _
      have h2 : ‖q‖ ^ (p.1 + p.2 + p.2) = ‖q‖ ^ p.1 * ‖q‖ ^ p.2 * ‖q‖ ^ p.2 := by
        rw [← pow_add, ← pow_add]
      have h3 : ‖q‖ ^ p.2 ≤ 1 := pow_le_one₀ (norm_nonneg q) (le_of_lt hq1)
      calc ‖c (p.1 + p.2) p.2‖ * ‖w‖ ^ p.2 * ‖q‖ ^ (p.1 + p.2 + p.2)
          = ‖c (p.1 + p.2) p.2‖ * (‖q‖ ^ p.1 * (‖q‖ * ‖w‖) ^ p.2 * ‖q‖ ^ p.2) := by
            rw [h2, mul_pow]
            ring
        _ ≤ B * (‖q‖ ^ p.1 * (‖q‖ * ‖w‖) ^ p.2 * 1) := by
            refine mul_le_mul h1 ?_ (by positivity) hB
            exact mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = B * (‖q‖ ^ p.1 * (‖q‖ * ‖w‖) ^ p.2) := by ring
    · rw [if_neg fun hcon => hg hcon.1, norm_zero]
      positivity

set_option maxHeartbeats 4000000 in
private lemma summable_betaT_ES (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) : Summable (betaT_ES c w q) := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hw hqw
  have hρ : ‖w⁻¹‖ < 1 := norm_inv_lt_one_of_one_lt_norm hw
  refine summable_of_shift_bound_ES (C := B) (norm_nonneg q) hq1 (norm_nonneg w⁻¹) hρ ?_ ?_
  · intro p hp
    simp only [betaT_ES]
    exact if_neg fun hg => hp hg.2
  · intro p
    simp only [betaT_ES, shiftPair_ES]
    by_cases hg : 1 ≤ p.2
    · rw [if_pos ⟨hg, by omega⟩]
      have h0 : p.1 + p.2 - p.2 = p.1 := by omega
      rw [h0, norm_mul, norm_mul, norm_pow, norm_pow]
      have h1 : ‖c (p.1 + p.2) p.2‖ ≤ B := hc _ _
      calc ‖c (p.1 + p.2) p.2‖ * ‖w⁻¹‖ ^ p.2 * ‖q‖ ^ p.1
          ≤ B * ‖w⁻¹‖ ^ p.2 * ‖q‖ ^ p.1 := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = B * (‖q‖ ^ p.1 * ‖w⁻¹‖ ^ p.2) := by ring
    · rw [if_neg fun hcon => hg hcon.1, norm_zero]
      positivity

private lemma norm_neg_two_le_one_ES : ‖(-2 : K)‖ ≤ 1 := by
  rw [norm_neg]
  have h3 : ((2 : ℕ) : K) = (2 : K) := by norm_num
  have h4 := norm_natCast_le_one K 2
  rwa [h3] at h4

set_option maxHeartbeats 4000000 in
private lemma summable_gammaT_ES (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) : Summable (gammaT_ES c q) := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hw hqw
  refine summable_of_shift_bound_ES (C := B) (norm_nonneg q) hq1 (norm_nonneg q) hq1 ?_ ?_
  · intro p hp
    simp only [gammaT_ES]
    exact if_neg fun hg => hp hg.2
  · intro p
    simp only [gammaT_ES, shiftPair_ES]
    by_cases hg : 1 ≤ p.2
    · rw [if_pos ⟨hg, by omega⟩]
      rw [norm_mul, norm_mul, norm_pow]
      have h1 : ‖c (p.1 + p.2) p.2‖ ≤ B := hc _ _
      calc ‖(-2 : K)‖ * ‖c (p.1 + p.2) p.2‖ * ‖q‖ ^ (p.1 + p.2)
          ≤ 1 * B * ‖q‖ ^ (p.1 + p.2) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul norm_neg_two_le_one_ES h1 (norm_nonneg _) zero_le_one
        _ = B * (‖q‖ ^ p.1 * ‖q‖ ^ p.2) := by rw [one_mul, ← pow_add]
    · rw [if_neg fun hcon => hg hcon.1, norm_zero]
      positivity

private lemma summable_hubT_ES (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) : Summable (hubT_ES c w q) := by
  have hw0 : w ≠ 0 := ne_zero_of_one_lt_norm hw
  exact (((summable_alphaT_ES hB hc hw hqw).add (summable_betaT_ES hB hc hw hqw)).add
    (summable_gammaT_ES hB hc hw hqw)).congr fun p => (hubT_eq_ES hq0 hw0 p).symm

end Families

section Regroup

variable {c : ℕ → ℕ → K} {w q : K} {B : ℝ}

set_option maxHeartbeats 4000000 in
private lemma tsum_alphaT_ES (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    ∑' p : ℕ × ℕ, alphaT_ES c w q p = ∑' M : ℕ, specAlpha c w M * q ^ M := by
  rw [tsum_prod_eq_tsum_sum_antidiagonal_ES (summable_alphaT_ES hB hc hw hqw)]
  refine tsum_congr fun M => ?_
  simp only [specAlpha]
  rw [Finset.sum_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpM : p.1 + p.2 = M := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  simp only [alphaT_ES]
  by_cases hg : 1 ≤ p.2 ∧ p.2 ≤ p.1
  · rw [if_pos hg, if_pos hg, hpM]
  · rw [if_neg hg, if_neg hg, zero_mul]

set_option maxHeartbeats 4000000 in
private lemma tsum_betaT_ES (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    ∑' p : ℕ × ℕ, betaT_ES c w q p = ∑' M : ℕ, specTail c w M * q ^ M := by
  have hsupport : Function.support (betaT_ES c w q) ⊆ Set.range shiftPair_ES := by
    intro p hp
    by_contra hcon
    refine hp ?_
    simp only [betaT_ES]
    refine if_neg fun hg => hcon (mem_range_shiftPair_ES hg.2)
  rw [← shiftPair_injective_ES.tsum_eq hsupport]
  have hcomp : Summable fun p : ℕ × ℕ => betaT_ES c w q (shiftPair_ES p) :=
    (summable_betaT_ES hB hc hw hqw).comp_injective shiftPair_injective_ES
  rw [hcomp.tsum_prod]
  refine tsum_congr fun M => ?_
  simp only [specTail]
  rw [← tsum_mul_right]
  refine tsum_congr fun k => ?_
  simp only [betaT_ES, shiftPair_ES]
  by_cases hk : 1 ≤ k
  · rw [if_pos ⟨hk, by omega⟩, if_pos hk]
    have h0 : M + k - k = M := by omega
    rw [h0]
  · rw [if_neg fun hcon => hk hcon.1, if_neg hk, zero_mul]

set_option maxHeartbeats 4000000 in
private lemma tsum_gammaT_ES (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    ∑' p : ℕ × ℕ, gammaT_ES c q p = ∑' M : ℕ, specGamma c M * q ^ M := by
  rw [(summable_gammaT_ES hB hc hw hqw).tsum_prod]
  refine tsum_congr fun N => ?_
  have hvanish : ∀ k ∉ Finset.Icc 1 N, gammaT_ES c q (N, k) = 0 := by
    intro k hk
    simp only [gammaT_ES]
    refine if_neg fun hg => hk (Finset.mem_Icc.mpr ⟨hg.1, hg.2⟩)
  rw [tsum_eq_sum hvanish]
  simp only [specGamma]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_Icc.mp hk
  simp only [gammaT_ES]
  rw [if_pos ⟨hk'.1, hk'.2⟩]

set_option maxHeartbeats 4000000 in

private lemma tsum_hubT_ES (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    ∑' p : ℕ × ℕ, hubT_ES c w q p
      = ∑' M : ℕ,
          (∑ k ∈ Finset.Icc 1 M, c M k * ((q * w) ^ k + (q * w)⁻¹ ^ k - 2)) * q ^ M := by
  rw [(summable_hubT_ES hB hc hq0 hw hqw).tsum_prod]
  refine tsum_congr fun N => ?_
  have hvanish : ∀ k ∉ Finset.Icc 1 N, hubT_ES c w q (N, k) = 0 := by
    intro k hk
    simp only [hubT_ES]
    refine if_neg fun hg => hk (Finset.mem_Icc.mpr ⟨hg.1, hg.2⟩)
  rw [tsum_eq_sum hvanish, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_Icc.mp hk
  simp only [hubT_ES]
  rw [if_pos ⟨hk'.1, hk'.2⟩]

end Regroup

section SpecBounds

variable {c : ℕ → ℕ → K} {w q : K} {B : ℝ}

private lemma norm_specAlpha_le_ES (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B) (hw : 1 ≤ ‖w‖) (M : ℕ) :
    ‖specAlpha c w M‖ ≤ B * ‖w‖ ^ M := by
  refine norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg hB (pow_nonneg (norm_nonneg _) _)) fun p hp => ?_
  have hmem := Finset.mem_filter.mp hp
  have hanti := Finset.HasAntidiagonal.mem_antidiagonal.mp hmem.1
  have hple : p.2 ≤ M := by omega
  rw [norm_mul, norm_pow]
  have h1 : ‖c p.1 p.2‖ ≤ B := hc _ _
  have h2 : ‖w‖ ^ p.2 ≤ ‖w‖ ^ M := pow_le_pow_right₀ hw hple
  have h3 : (0 : ℝ) ≤ ‖w‖ ^ p.2 := pow_nonneg (norm_nonneg _) _
  nlinarith

private lemma norm_specGamma_le_ES (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B) (M : ℕ) :
    ‖specGamma c M‖ ≤ B := by
  refine norm_sum_le_of_forall_le_of_nonneg hB fun k _ => ?_
  rw [norm_mul]
  calc ‖(-2 : K)‖ * ‖c M k‖
      ≤ 1 * ‖c M k‖ := mul_le_mul_of_nonneg_right norm_neg_two_le_one_ES (norm_nonneg _)
    _ = ‖c M k‖ := one_mul _
    _ ≤ B := hc M k

private lemma summable_specAlpha_mul_pow_ES (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    Summable fun M : ℕ => specAlpha c w M * q ^ M := by
  have hr0 : (0 : ℝ) ≤ ‖q‖ * ‖w‖ := mul_nonneg (norm_nonneg q) (norm_nonneg w)
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun M => norm_nonneg _) (fun M => ?_)
    ((summable_geometric_of_lt_one hr0 hqw).mul_left B))
  rw [norm_mul, norm_pow]
  have h1 := norm_specAlpha_le_ES hB hc (le_of_lt hw) M
  have h2 : ‖w‖ ^ M * ‖q‖ ^ M = (‖q‖ * ‖w‖) ^ M := by rw [mul_pow]; ring
  have h3 : (0 : ℝ) ≤ ‖q‖ ^ M := pow_nonneg (norm_nonneg q) _
  calc ‖specAlpha c w M‖ * ‖q‖ ^ M ≤ (B * ‖w‖ ^ M) * ‖q‖ ^ M :=
        mul_le_mul_of_nonneg_right h1 h3
    _ = B * (‖q‖ * ‖w‖) ^ M := by rw [mul_assoc, h2]

private lemma summable_specTail_mul_pow_ES (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    Summable fun M : ℕ => specTail c w M * q ^ M := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hw hqw
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun M => norm_nonneg _) (fun M => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg q) hq1).mul_left B))
  rw [norm_mul, norm_pow]
  have h1 := norm_specTail_le hB hc hw M
  have h3 : (0 : ℝ) ≤ ‖q‖ ^ M := pow_nonneg (norm_nonneg q) _
  exact mul_le_mul_of_nonneg_right h1 h3

private lemma summable_specGamma_mul_pow_ES (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    Summable fun M : ℕ => specGamma c M * q ^ M := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hw hqw
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun M => norm_nonneg _) (fun M => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg q) hq1).mul_left B))
  rw [norm_mul, norm_pow]
  have h1 := norm_specGamma_le_ES (c := c) hB hc M
  have h3 : (0 : ℝ) ≤ ‖q‖ ^ M := pow_nonneg (norm_nonneg q) _
  exact mul_le_mul_of_nonneg_right h1 h3

private lemma summable_spec_series_ES (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    Summable fun M : ℕ => (specAlpha c w M + specTail c w M + specGamma c M) * q ^ M := by
  refine (((summable_specAlpha_mul_pow_ES hB hc hw hqw).add
    (summable_specTail_mul_pow_ES hB hc hw hqw)).add
    (summable_specGamma_mul_pow_ES hB hc hw hqw)).congr fun M => ?_
  ring

end SpecBounds

section AbstractMaster

set_option maxHeartbeats 4000000 in

theorem master_of_hasSum_qshift {B : ℝ} (hB : 0 ≤ B) (c : ℕ → ℕ → K)
    (hc : ∀ N k, ‖c N k‖ ≤ B) {g : K → K → K}
    (hinv : ∀ q w : K, q ≠ 0 → 1 < ‖w‖ → ‖q‖ * ‖w‖ < 1 → g q (q * w) = g q w)
    (hrepr : ∀ q w : K, q ≠ 0 → ‖q‖ < ‖w‖ → ‖q‖ * ‖w‖ < 1 → ‖w‖ ≠ 1 →
      HasSum (fun M : ℕ =>
        (∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2)) * q ^ M) (g q w)) :
    ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2)
        = specAlpha c w M + specTail c w M + specGamma c M := by
  intro M w hw
  have hw0 : w ≠ 0 := ne_zero_of_one_lt_norm hw
  have hwpos : (0 : ℝ) < ‖w‖ := lt_trans one_pos hw
  have hwne1 : ‖w‖ ≠ 1 := ne_of_gt hw

  have hq₀0 : w⁻¹ * w⁻¹ ≠ 0 := mul_ne_zero (inv_ne_zero hw0) (inv_ne_zero hw0)
  have hwinv_lt : ‖w⁻¹‖ < 1 := norm_inv_lt_one_of_one_lt_norm hw
  have hwinv_pos : (0 : ℝ) < ‖w⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hw0)
  have hq₀norm : ‖w⁻¹ * w⁻¹‖ = ‖w⁻¹‖ * ‖w⁻¹‖ := norm_mul _ _
  have hq₀1 : ‖w⁻¹ * w⁻¹‖ < 1 := by
    rw [hq₀norm]
    nlinarith

  have hregion : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖w⁻¹ * w⁻¹‖ → ‖q‖ * ‖w‖ < 1 := by
    intro q hq hqle
    have h1 : ‖w⁻¹‖ * ‖w‖ = 1 := by
      rw [norm_inv]
      field_simp
    have h2 : ‖q‖ ≤ ‖w⁻¹‖ * ‖w⁻¹‖ := by rwa [hq₀norm] at hqle
    nlinarith
  have hqlt_of : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖w⁻¹ * w⁻¹‖ → ‖q‖ < ‖w‖ := by
    intro q hq hqle
    have h1 : ‖q‖ < 1 := lt_of_le_of_lt hqle hq₀1
    linarith

  have ha : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖w⁻¹ * w⁻¹‖ →
      Summable fun N => (∑ k ∈ Finset.Icc 1 N, c N k * (w ^ k + w⁻¹ ^ k - 2)) * q ^ N := by
    intro q hq hqle
    exact (hrepr q w hq (hqlt_of q hq hqle) (hregion q hq hqle) hwne1).summable
  have hb : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖w⁻¹ * w⁻¹‖ →
      Summable fun N => (specAlpha c w N + specTail c w N + specGamma c N) * q ^ N := by
    intro q hq hqle
    exact summable_spec_series_ES hB hc hw (hregion q hq hqle)
  have heq : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖w⁻¹ * w⁻¹‖ →
      ∑' N, (∑ k ∈ Finset.Icc 1 N, c N k * (w ^ k + w⁻¹ ^ k - 2)) * q ^ N
        = ∑' N, (specAlpha c w N + specTail c w N + specGamma c N) * q ^ N := by
    intro q hq hqle
    have hqw : ‖q‖ * ‖w‖ < 1 := hregion q hq hqle
    have hq1 : ‖q‖ < 1 := lt_of_le_of_lt hqle hq₀1
    have hqlt : ‖q‖ < ‖w‖ := hqlt_of q hq hqle
    have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq

    have hqw_norm : ‖q * w‖ = ‖q‖ * ‖w‖ := norm_mul q w
    have hqw_lt1 : ‖q * w‖ < 1 := by rw [hqw_norm]; exact hqw
    have hqw_gt : ‖q‖ < ‖q * w‖ := by
      rw [hqw_norm]
      nlinarith [mul_pos hqpos (sub_pos.mpr hw)]
    have hq_qw : ‖q‖ * ‖q * w‖ < 1 := by
      rw [hqw_norm]
      have h := mul_lt_mul_of_pos_left hqw hqpos
      rw [mul_one] at h
      linarith
    have hqw_ne1 : ‖q * w‖ ≠ 1 := ne_of_lt hqw_lt1

    have hX := hrepr q w hq hqlt hqw hwne1
    have hXq := hrepr q (q * w) hq hqw_gt hq_qw hqw_ne1

    have hSα := summable_specAlpha_mul_pow_ES hB hc hw hqw
    have hSτ := summable_specTail_mul_pow_ES hB hc hw hqw
    have hSγ := summable_specGamma_mul_pow_ES hB hc hw hqw

    calc ∑' N, (∑ k ∈ Finset.Icc 1 N, c N k * (w ^ k + w⁻¹ ^ k - 2)) * q ^ N
        = g q w := hX.tsum_eq
      _ = g q (q * w) := (hinv q w hq hw hqw).symm
      _ = ∑' N, (∑ k ∈ Finset.Icc 1 N, c N k * ((q * w) ^ k + (q * w)⁻¹ ^ k - 2)) * q ^ N :=
          hXq.tsum_eq.symm
      _ = ∑' p : ℕ × ℕ, hubT_ES c w q p := (tsum_hubT_ES hB hc hq hw hqw).symm
      _ = ∑' p : ℕ × ℕ, (alphaT_ES c w q p + betaT_ES c w q p + gammaT_ES c q p) :=
          tsum_congr fun p => hubT_eq_ES hq hw0 p
      _ = (∑' p : ℕ × ℕ, (alphaT_ES c w q p + betaT_ES c w q p)) + ∑' p : ℕ × ℕ, gammaT_ES c q p :=
          ((summable_alphaT_ES hB hc hw hqw).add (summable_betaT_ES hB hc hw hqw)).tsum_add
            (summable_gammaT_ES hB hc hw hqw)
      _ = ((∑' p : ℕ × ℕ, alphaT_ES c w q p) + ∑' p : ℕ × ℕ, betaT_ES c w q p)
            + ∑' p : ℕ × ℕ, gammaT_ES c q p := by
          rw [(summable_alphaT_ES hB hc hw hqw).tsum_add (summable_betaT_ES hB hc hw hqw)]
      _ = ((∑' M, specAlpha c w M * q ^ M) + ∑' M, specTail c w M * q ^ M)
            + ∑' M, specGamma c M * q ^ M := by
          rw [tsum_alphaT_ES hB hc hw hqw, tsum_betaT_ES hB hc hw hqw, tsum_gammaT_ES hB hc hw hqw]
      _ = (∑' M, (specAlpha c w M * q ^ M + specTail c w M * q ^ M))
            + ∑' M, specGamma c M * q ^ M := by
          rw [hSα.tsum_add hSτ]
      _ = ∑' M, ((specAlpha c w M * q ^ M + specTail c w M * q ^ M)
            + specGamma c M * q ^ M) := by
          rw [(hSα.add hSτ).tsum_add hSγ]
      _ = ∑' N, (specAlpha c w N + specTail c w N + specGamma c N) * q ^ N :=
          tsum_congr fun N => by ring
  exact rowCoeff_eq_of_forall_tsum_eq_ES hq₀0 hq₀1 ha hb heq M

end AbstractMaster

section Region

variable {q u v : K}

lemma offLattice_of_norm_annulus (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    (hlo : ‖q‖ < ‖u‖) (hhi : ‖q‖ * ‖u‖ < 1) (hne : ‖u‖ ≠ 1) : OffLattice q u := by
  intro n hn
  have hq_pos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hu_pos : (0 : ℝ) < ‖u‖ := lt_trans hq_pos hlo
  have hnorm : ‖q‖ ^ n * ‖u‖ = 1 := by
    have h1 := congrArg norm hn
    rwa [norm_mul, norm_zpow, norm_one] at h1
  rcases lt_trichotomy n 0 with hneg | hzero | hpos
  ·
    have h2 : ‖q‖ ^ (-1 : ℤ) ≤ ‖q‖ ^ n :=
      zpow_le_zpow_right_of_le_one₀ hq_pos (le_of_lt hq1) (by omega)
    rw [zpow_neg_one] at h2
    have h3 : ‖q‖⁻¹ * ‖u‖ ≤ ‖q‖ ^ n * ‖u‖ := mul_le_mul_of_nonneg_right h2 (le_of_lt hu_pos)
    rw [hnorm] at h3
    have h4 : ‖u‖ ≤ ‖q‖ := by
      have h5 : ‖q‖ * (‖q‖⁻¹ * ‖u‖) ≤ ‖q‖ * 1 := mul_le_mul_of_nonneg_left h3 (le_of_lt hq_pos)
      rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hq_pos), one_mul, mul_one] at h5
    linarith
  ·
    rw [hzero, zpow_zero, one_mul] at hnorm
    exact hne hnorm
  ·
    have h2 : ‖q‖ ^ n ≤ ‖q‖ ^ (1 : ℤ) :=
      zpow_le_zpow_right_of_le_one₀ hq_pos (le_of_lt hq1) (by omega)
    rw [zpow_one] at h2
    have h3 : ‖q‖ ^ n * ‖u‖ ≤ ‖q‖ * ‖u‖ := mul_le_mul_of_nonneg_right h2 (le_of_lt hu_pos)
    rw [hnorm] at h3
    linarith

lemma expansionRegion_of_spectator {q' w v : K} (hq'0 : q' ≠ 0)
    (hlo : ‖q'‖ < ‖w‖) (hhi : ‖q'‖ * ‖w‖ < 1) (hwne : ‖w‖ ≠ 1)
    (hv : ‖v‖ = 1) (hv1 : v ≠ 1) : ExpansionRegion q' w v := by
  have hq'pos : (0 : ℝ) < ‖q'‖ := norm_pos_iff.mpr hq'0
  have hwpos : (0 : ℝ) < ‖w‖ := lt_trans hq'pos hlo
  have hw0 : w ≠ 0 := norm_pos_iff.mp hwpos
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv
    exact zero_ne_one hv
  have hq'1 : ‖q'‖ < 1 := by
    by_cases hge : 1 ≤ ‖q'‖
    · exfalso
      have h2 : ‖w‖ ≤ ‖q'‖ * ‖w‖ := le_mul_of_one_le_left (le_of_lt hwpos) hge
      have h3 : ‖w‖ < 1 := lt_of_le_of_lt h2 hhi
      linarith
    · exact not_le.mp hge
  have hmul_norm : ‖w * v‖ = ‖w‖ := by rw [norm_mul, hv, mul_one]
  have hdiv_norm : ‖w * v⁻¹‖ = ‖w‖ := by rw [norm_mul, norm_inv, hv, inv_one, mul_one]
  have hofflat_w : OffLattice q' w := offLattice_of_norm_annulus hq'0 hq'1 hlo hhi hwne
  have hofflat_v : OffLattice q' v := offLattice_of_norm_eq_one hq'0 hq'1 hv hv1
  have hofflat_mul : OffLattice q' (w * v) := by
    refine offLattice_of_norm_annulus hq'0 hq'1 ?_ ?_ ?_ <;> rw [hmul_norm]
    exacts [hlo, hhi, hwne]
  have hofflat_div : OffLattice q' (w * v⁻¹) := by
    refine offLattice_of_norm_annulus hq'0 hq'1 ?_ ?_ ?_ <;> rw [hdiv_norm]
    exacts [hlo, hhi, hwne]
  refine ⟨⟨hq'0, hw0, hv0, hofflat_w, hofflat_v, hofflat_mul, hofflat_div⟩,
    hq'1, hlo, hhi, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv]; exact hq'1
  · rw [hv, mul_one]; exact hq'1
  · rw [hmul_norm]; exact hlo
  · rw [hmul_norm]; exact hhi
  · rw [hdiv_norm]; exact hlo
  · rw [hdiv_norm]; exact hhi

end Region

section SumReduction

variable {q u v : K}

set_option maxHeartbeats 4000000 in

theorem symAdd_sum_of_rowExpansion {B : ℝ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K} (ha : ∀ M k j, ‖a M k j‖ ≤ B)
    (hexp : ∀ q' u' v' : K, ExpansionRegion q' u' v' →
      HasSum (fun M : ℕ =>
        (∑ k ∈ Finset.Icc 1 M,
            (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k + u'⁻¹ ^ k - 2)) * q' ^ M)
        (addDefectSum q' u' v'))
    (hreg : ExpansionRegion q u v) :
    (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v) := by
  have hq0 : q ≠ 0 := hreg.params.q_ne_zero
  have hq1 : ‖q‖ < 1 := hreg.norm_q_lt_one
  have hv0 : v ≠ 0 := hreg.params.v_ne_zero
  refine symAdd_sum_of_laurentRows hq0 hq1 hB ha ?_ hv0 (hexp q u v hreg)

  intro n
  have hsp_norm : ‖unitSpectator q n‖ = 1 := norm_unitSpectator hq0 hq1 n
  have hsp_ne1 : unitSpectator q n ≠ 1 := unitSpectator_ne_one hq0 n
  refine master_of_hasSum_qshift hB (spectatorRows s a (unitSpectator q n))
    (fun N k => norm_spectatorRows_le hB ha hsp_norm N k)
    (g := fun q' u' => addDefectSum q' u' (unitSpectator q n))
    (fun q' w' hq'0 _hw' _hq'w' => addDefectSum_q_mul_left hq'0) ?_
  intro q' w' hq'0 hlo hhi hwne
  exact hexp q' w' (unitSpectator q n)
    (expansionRegion_of_spectator hq'0 hlo hhi hwne hsp_norm hsp_ne1)

end SumReduction

end TateCurve

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "eq_zero_of_master_rows unitSpectator norm_unitSpectator unitSpectator_ne_one spectatorRows norm_spectatorRows_le symAdd_sum_of_laurentRows symAdd_prod_of_laurentRows symSumNum symProdNum OffLattice OffLattice.zpow_mul OffLattice.inv AddParams AddParams.swap pointX_inv_mul pointX_inv_mul_inv pointX_q_inv_mul addDefectSum addDefectProd addDefectSum_q_mul_left addDefectProd_q_mul_left nodal_symSum offLattice_of_norm_eq_one addParams_of_norm_one_spectator norm_mul_eq_of_norm_eq_one norm_mul_inv_eq_of_norm_eq_one specTail specAlpha specGamma summable_specTail_term norm_specTail_le spec_eq_zero_of_master summable_norm_a₄Series summable_norm_a₆Series summable_norm_xSeries summable_norm_ySeries ne_zero_of_one_lt_norm norm_q_lt_one_of_qshift norm_inv_lt_one_of_one_lt_norm cauchyMul_two tent xfun_mul_Fz_eq_tent cauchyMul cauchyMul_zero cauchyMul_one qSeries_mul summable_norm_cauchyMul xCoeffFull xCoeffFull_zero xCoeffFull_succ yCoeffFull yCoeffFull_zero yCoeffFull_succ a₄Coeff a₄Coeff_zero a₄Coeff_succ a₆Coeff a₆Coeff_zero a₆Coeff_succ xfun yfun pointX pointY term term_zero summable_term coeffSum b a₄ a₆ curve curve_a₁ curve_a₃ xDivTerm yDivTerm xCoeff yCoeff pointX_inv pointX_q_mul pointX_zpow_mul pointPsiTwo addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff psiCoeffFull addDefectDiffCoeff LatticeRep OnHalfLattice MuTranslation pointX_qExpansion pointY_qExpansion pointY_q_mul pointY_inv pointY_zpow_mul"
p2m_open "TateCurve~tsum_succ_prod_eq_tsum_divisors"

open scoped NNReal

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q u v : K}

section Helpers

private lemma nnnorm_lt_one_of_norm_lt_one_ES2 {x : K} (h : ‖x‖ < 1) : ‖x‖₊ < 1 := by
  exact_mod_cast h

private lemma region_nnnorm_pair_ES2 {w : K} (hq0 : q ≠ 0) (hlo : ‖q‖ < ‖w‖)
    (hhi : ‖q‖ * ‖w‖ < 1) : ‖q * w‖₊ < 1 ∧ ‖q * w⁻¹‖₊ < 1 := by
  have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hwpos : (0 : ℝ) < ‖w‖ := lt_trans hqpos hlo
  constructor
  · have h1 : ‖q * w‖ < 1 := by rw [norm_mul]; exact hhi
    exact nnnorm_lt_one_of_norm_lt_one_ES2 h1
  · have h2 : ‖q * w⁻¹‖ < 1 := by
      rw [norm_mul, norm_inv, ← div_eq_mul_inv]
      exact (div_lt_one hwpos).mpr hlo
    exact nnnorm_lt_one_of_norm_lt_one_ES2 h2

private lemma hasSum_of_eq_tsum_ES2 {c : ℕ → K} {x : K}
    (hn : Summable fun N => ‖c N * q ^ N‖) (hx : x = ∑' N : ℕ, c N * q ^ N) :
    HasSum (fun N => c N * q ^ N) x := by
  rw [hx]; exact hn.of_norm.hasSum

private lemma hasSum_qSeries_mul_ES2 {c d : ℕ → K} {x y : K}
    (hc : Summable fun N => ‖c N * q ^ N‖) (hd : Summable fun N => ‖d N * q ^ N‖)
    (hx : HasSum (fun N => c N * q ^ N) x) (hy : HasSum (fun N => d N * q ^ N) y) :
    HasSum (fun N => cauchyMul c d N * q ^ N) (x * y) := by
  have hval : x * y = ∑' N : ℕ, cauchyMul c d N * q ^ N := by
    rw [← hx.tsum_eq, ← hy.tsum_eq]
    exact qSeries_mul hc hd
  rw [hval]
  exact ((summable_norm_cauchyMul hc hd).of_norm).hasSum

private lemma hasSum_congr_fun_ES2 {f g : ℕ → K} {x : K} (h : HasSum f x)
    (heq : ∀ N, g N = f N) : HasSum g x := by
  have hfg : g = f := funext heq
  rw [hfg]; exact h

end Helpers

section Coefficients

variable (u v)
variable {u v}

theorem addDefectSumCoeff_zero (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u * v ≠ 1) (huv' : u * v⁻¹ ≠ 1) :
    addDefectSumCoeff u v 0 = 0 := by
  have hnodal := nodal_symSum (K := K) hu0 hv0 hu1 hv1 huv huv'
  simp only [addDefectSumCoeff, cauchyMul_zero, xCoeffFull_zero, a₄Coeff_zero, a₆Coeff_zero]
  linear_combination hnodal

end Coefficients

section Expansion

set_option maxHeartbeats 3200000 in

theorem addDefectSum_qExpansion (hreg : ExpansionRegion q u v) :
    HasSum (fun N : ℕ => addDefectSumCoeff u v N * q ^ N) (addDefectSum q u v) := by

  have hq0 : q ≠ 0 := hreg.params.q_ne_zero
  have hu0 : u ≠ 0 := hreg.params.u_ne_zero
  have hv0 : v ≠ 0 := hreg.params.v_ne_zero
  have hm0 : u * v ≠ 0 := mul_ne_zero hu0 hv0
  have hd0 : u * v⁻¹ ≠ 0 := mul_ne_zero hu0 (inv_ne_zero hv0)
  have hq1 : ‖q‖₊ < 1 := nnnorm_lt_one_of_norm_lt_one_ES2 hreg.norm_q_lt_one
  obtain ⟨hqu, hqu'⟩ := region_nnnorm_pair_ES2 hq0 hreg.u_lo hreg.u_hi
  obtain ⟨hqv, hqv'⟩ := region_nnnorm_pair_ES2 hq0 hreg.v_lo hreg.v_hi
  obtain ⟨hqm, hqm'⟩ := region_nnnorm_pair_ES2 hq0 hreg.mul_lo hreg.mul_hi
  obtain ⟨hqd, hqd'⟩ := region_nnnorm_pair_ES2 hq0 hreg.div_lo hreg.div_hi

  have nP : Summable fun N => ‖xCoeffFull u N * q ^ N‖ := summable_norm_xSeries hq1 hqu hqu'
  have nQ : Summable fun N => ‖xCoeffFull v N * q ^ N‖ := summable_norm_xSeries hq1 hqv hqv'
  have nM : Summable fun N => ‖xCoeffFull (u * v) N * q ^ N‖ :=
    summable_norm_xSeries hq1 hqm hqm'
  have nD : Summable fun N => ‖xCoeffFull (u * v⁻¹) N * q ^ N‖ :=
    summable_norm_xSeries hq1 hqd hqd'
  have nA4 : Summable fun N => ‖a₄Coeff (K := K) N * q ^ N‖ := summable_norm_a₄Series hq1
  have nA6 : Summable fun N => ‖a₆Coeff (K := K) N * q ^ N‖ := summable_norm_a₆Series hq1

  have hXu : HasSum (fun N => xCoeffFull u N * q ^ N) (pointX q u) :=
    hasSum_of_eq_tsum_ES2 nP
      (pointX_eq_tsum hq0 hq1 hu0 hreg.params.offLattice_u hqu hqu')
  have hXv : HasSum (fun N => xCoeffFull v N * q ^ N) (pointX q v) :=
    hasSum_of_eq_tsum_ES2 nQ
      (pointX_eq_tsum hq0 hq1 hv0 hreg.params.offLattice_v hqv hqv')
  have hXm : HasSum (fun N => xCoeffFull (u * v) N * q ^ N) (pointX q (u * v)) :=
    hasSum_of_eq_tsum_ES2 nM
      (pointX_eq_tsum hq0 hq1 hm0 hreg.params.offLattice_mul hqm hqm')
  have hXd : HasSum (fun N => xCoeffFull (u * v⁻¹) N * q ^ N) (pointX q (u * v⁻¹)) :=
    hasSum_of_eq_tsum_ES2 nD
      (pointX_eq_tsum hq0 hq1 hd0 hreg.params.offLattice_div hqd hqd')
  have hA4 : HasSum (fun N => a₄Coeff (K := K) N * q ^ N) (a₄ q) :=
    hasSum_of_eq_tsum_ES2 nA4 (a₄_eq_tsum hq1)
  have hA6 : HasSum (fun N => a₆Coeff (K := K) N * q ^ N) (a₆ q) :=
    hasSum_of_eq_tsum_ES2 nA6 (a₆_eq_tsum hq1)

  have nPP := summable_norm_cauchyMul nP nP
  have nPQ := summable_norm_cauchyMul nP nQ
  have nQQ := summable_norm_cauchyMul nQ nQ
  have hPP := hasSum_qSeries_mul_ES2 nP nP hXu hXu
  have hPQ := hasSum_qSeries_mul_ES2 nP nQ hXu hXv
  have hQQ := hasSum_qSeries_mul_ES2 nQ nQ hXv hXv

  have H1 := hasSum_qSeries_mul_ES2 nM nPP hXm hPP
  have H2 := hasSum_qSeries_mul_ES2 nM nPQ hXm hPQ
  have H3 := hasSum_qSeries_mul_ES2 nM nQQ hXm hQQ
  have H4 := hasSum_qSeries_mul_ES2 nD nPP hXd hPP
  have H5 := hasSum_qSeries_mul_ES2 nD nPQ hXd hPQ
  have H6 := hasSum_qSeries_mul_ES2 nD nQQ hXd hQQ
  have H7 := hasSum_qSeries_mul_ES2 nP nPQ hXu hPQ
  have H8 := hasSum_qSeries_mul_ES2 nP nQQ hXu hQQ
  have H10 := hasSum_qSeries_mul_ES2 nA4 nP hA4 hXu
  have H11 := hasSum_qSeries_mul_ES2 nA4 nQ hA4 hXv

  have S1 := H1.sub (H2.mul_left 2)
  have S2 := S1.add H3
  have S3 := S2.add H4
  have S4 := S3.sub (H5.mul_left 2)
  have S5 := S4.add H6
  have S6 := S5.sub (H7.mul_left 2)
  have S7 := S6.sub (H8.mul_left 2)
  have S8 := S7.sub hPQ
  have S9 := S8.sub (H10.mul_left 2)
  have S10 := S9.sub (H11.mul_left 2)
  have Hbig := S10.sub (hA6.mul_left 4)
  have hdefect : addDefectSum q u v
      = pointX q (u * v) * (pointX q u * pointX q u)
        - 2 * (pointX q (u * v) * (pointX q u * pointX q v))
        + pointX q (u * v) * (pointX q v * pointX q v)
        + pointX q (u * v⁻¹) * (pointX q u * pointX q u)
        - 2 * (pointX q (u * v⁻¹) * (pointX q u * pointX q v))
        + pointX q (u * v⁻¹) * (pointX q v * pointX q v)
        - 2 * (pointX q u * (pointX q u * pointX q v))
        - 2 * (pointX q u * (pointX q v * pointX q v))
        - pointX q u * pointX q v
        - 2 * (a₄ q * pointX q u)
        - 2 * (a₄ q * pointX q v)
        - 4 * a₆ q := by
    simp only [addDefectSum, symSumNum]
    ring
  rw [hdefect]
  exact hasSum_congr_fun_ES2 Hbig fun N => by
    simp only [addDefectSumCoeff]
    ring

end Expansion

section Bridge

theorem rowExpansion_of_coeff_eq {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (hrow : ∀ q' u' v' : K, ExpansionRegion q' u' v' → ∀ M : ℕ,
      addDefectSumCoeff u' v' M
        = ∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k + u'⁻¹ ^ k - 2)) :
    ∀ q' u' v' : K, ExpansionRegion q' u' v' →
      HasSum (fun M : ℕ =>
        (∑ k ∈ Finset.Icc 1 M,
            (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k + u'⁻¹ ^ k - 2)) * q' ^ M)
        (addDefectSum q' u' v') := by
  intro q' u' v' hreg'
  refine hasSum_congr_fun_ES2 (addDefectSum_qExpansion hreg') fun M => ?_
  rw [hrow q' u' v' hreg' M]

theorem symAdd_sum_of_coeff_eq {B : ℝ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K} (ha : ∀ M k j, ‖a M k j‖ ≤ B)
    (hrow : ∀ q' u' v' : K, ExpansionRegion q' u' v' → ∀ M : ℕ,
      addDefectSumCoeff u' v' M
        = ∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k + u'⁻¹ ^ k - 2))
    (hreg : ExpansionRegion q u v) :
    (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v) :=
  symAdd_sum_of_rowExpansion hB ha (rowExpansion_of_coeff_eq hrow) hreg

end Bridge

end TateCurve

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

namespace TateCurve
p2m_export "TateCurve" "eq_zero_of_master_rows unitSpectator norm_unitSpectator unitSpectator_ne_one spectatorRows norm_spectatorRows_le symAdd_sum_of_laurentRows symAdd_prod_of_laurentRows symSumNum symProdNum OffLattice OffLattice.zpow_mul OffLattice.inv AddParams AddParams.swap pointX_inv_mul pointX_inv_mul_inv pointX_q_inv_mul addDefectSum addDefectProd addDefectSum_q_mul_left addDefectProd_q_mul_left nodal_symSum offLattice_of_norm_eq_one addParams_of_norm_one_spectator norm_mul_eq_of_norm_eq_one norm_mul_inv_eq_of_norm_eq_one specTail specAlpha specGamma summable_specTail_term norm_specTail_le spec_eq_zero_of_master summable_norm_a₄Series summable_norm_a₆Series summable_norm_xSeries summable_norm_ySeries ne_zero_of_one_lt_norm norm_q_lt_one_of_qshift norm_inv_lt_one_of_one_lt_norm cauchyMul_two tent xfun_mul_Fz_eq_tent cauchyMul cauchyMul_zero cauchyMul_one qSeries_mul summable_norm_cauchyMul xCoeffFull xCoeffFull_zero xCoeffFull_succ yCoeffFull yCoeffFull_zero yCoeffFull_succ a₄Coeff a₄Coeff_zero a₄Coeff_succ a₆Coeff a₆Coeff_zero a₆Coeff_succ xfun yfun pointX pointY term term_zero summable_term coeffSum b a₄ a₆ curve curve_a₁ curve_a₃ xDivTerm yDivTerm xCoeff yCoeff pointX_inv pointX_q_mul pointX_zpow_mul pointPsiTwo addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff psiCoeffFull addDefectDiffCoeff LatticeRep OnHalfLattice MuTranslation pointX_qExpansion pointY_qExpansion pointY_q_mul pointY_inv pointY_zpow_mul"
p2m_open "TateCurve~tsum_succ_prod_eq_tsum_divisors"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q u v : K}

section Eval

theorem xCoeff_one (w : K) : xCoeff w 1 = w + w⁻¹ - 2 := by
  rw [xCoeff, Nat.divisors_one, Finset.sum_singleton, xDivTerm]
  push_cast
  ring

theorem xCoeff_two (w : K) : xCoeff w 2 = (w + w⁻¹ - 2) + 2 * (w ^ 2 + w⁻¹ ^ 2 - 2) := by
  have h2 : (2 : ℕ).divisors = {1, 2} := by decide
  have h12 : (1 : ℕ) ∉ ({2} : Finset ℕ) := by decide
  rw [xCoeff, h2, Finset.sum_insert h12, Finset.sum_singleton, xDivTerm, xDivTerm]
  push_cast
  ring

theorem xCoeffFull_one (w : K) : xCoeffFull w 1 = w + w⁻¹ - 2 := by
  have h : xCoeffFull w 1 = xCoeff w 1 := xCoeffFull_succ w 0
  rw [h, xCoeff_one]

theorem xCoeffFull_two (w : K) :
    xCoeffFull w 2 = (w + w⁻¹ - 2) + 2 * (w ^ 2 + w⁻¹ ^ 2 - 2) := by
  have h : xCoeffFull w 2 = xCoeff w 2 := xCoeffFull_succ w 1
  rw [h, xCoeff_two]

theorem a₄Coeff_one : a₄Coeff (K := K) 1 = -5 := by
  have h : a₄Coeff (K := K) 1 = -(∑ d ∈ (1 : ℕ).divisors, ((5 * d ^ 3 : ℕ) : K)) :=
    a₄Coeff_succ 0
  rw [h, Nat.divisors_one, Finset.sum_singleton]
  norm_num

theorem a₆Coeff_one : a₆Coeff (K := K) 1 = -1 := by
  have h : a₆Coeff (K := K) 1 = -(∑ d ∈ (1 : ℕ).divisors, ((b d : ℕ) : K)) := a₆Coeff_succ 0
  rw [h, Nat.divisors_one, Finset.sum_singleton]
  norm_num [b]

theorem a₄Coeff_two : a₄Coeff (K := K) 2 = -45 := by
  have h : a₄Coeff (K := K) 2 = -(∑ d ∈ (2 : ℕ).divisors, ((5 * d ^ 3 : ℕ) : K)) :=
    a₄Coeff_succ 1
  have h2 : (2 : ℕ).divisors = {1, 2} := by decide
  have h12 : (1 : ℕ) ∉ ({2} : Finset ℕ) := by decide
  rw [h, h2, Finset.sum_insert h12, Finset.sum_singleton]
  norm_num

theorem a₆Coeff_two : a₆Coeff (K := K) 2 = -23 := by
  have h : a₆Coeff (K := K) 2 = -(∑ d ∈ (2 : ℕ).divisors, ((b d : ℕ) : K)) := a₆Coeff_succ 1
  have h2 : (2 : ℕ).divisors = {1, 2} := by decide
  have h12 : (1 : ℕ) ∉ ({2} : Finset ℕ) := by decide
  rw [h, h2, Finset.sum_insert h12, Finset.sum_singleton]
  norm_num [b]

theorem xfun_mul_lin {w : K} (hw0 : w ≠ 0) (hw1 : w ≠ 1) : xfun w * (w + w⁻¹ - 2) = 1 := by
  have h1w : (1 : K) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  rw [xfun]
  field_simp
  ring

end Eval

section NeOne

namespace AddParams p2m_export "TateCurve.AddParams" "swap inv_left inv_right q_mul_left q_mul_right v_ne_zero u_ne_zero offLattice_v q_ne_zero mk offLattice_div offLattice_u offLattice_mul" end AddParams
p2m_open_scoped "TateCurve.AddParams" in

lemma AddParams.u_ne_one (h : AddParams q u v) : u ≠ 1 := by
  have h0 := h.offLattice_u 0
  simpa using h0

p2m_open_scoped "TateCurve.AddParams" in

lemma AddParams.v_ne_one (h : AddParams q u v) : v ≠ 1 := by
  have h0 := h.offLattice_v 0
  simpa using h0

p2m_open_scoped "TateCurve.AddParams" in

lemma AddParams.mul_ne_one (h : AddParams q u v) : u * v ≠ 1 := by
  have h0 := h.offLattice_mul 0
  simpa using h0

p2m_open_scoped "TateCurve.AddParams" in

lemma AddParams.div_ne_one (h : AddParams q u v) : u * v⁻¹ ≠ 1 := by
  have h0 := h.offLattice_div 0
  simpa using h0

end NeOne

section Warmups

set_option maxHeartbeats 6400000 in

theorem addDefectSumCoeff_one_eq_zero (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u * v ≠ 1) (huv' : u * v⁻¹ ≠ 1) :
    addDefectSumCoeff u v 1 = 0 := by
  have h1u : (1 : K) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have h1v : (1 : K) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
  have h1uv : (1 : K) - u * v ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  have h1uv' : (1 : K) - u * v⁻¹ ≠ 0 := sub_ne_zero.mpr (Ne.symm huv')
  have huv0 : u * v ≠ 0 := mul_ne_zero hu0 hv0
  have huv'0 : u * v⁻¹ ≠ 0 := mul_ne_zero hu0 (inv_ne_zero hv0)
  have hune : u ≠ v := fun h => huv' (by rw [h, mul_inv_cancel₀ hv0])
  have hsub : u - v ≠ 0 := sub_ne_zero.mpr hune
  have hsub' : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hune)
  simp only [addDefectSumCoeff, cauchyMul_one, cauchyMul_zero, xCoeffFull_zero, xCoeffFull_one,
    a₄Coeff_zero, a₆Coeff_zero, a₄Coeff_one, a₆Coeff_one, xfun, zero_mul, mul_zero, zero_add,
    add_zero]
  field_simp
  ring

set_option maxHeartbeats 12800000 in

theorem addDefectSumCoeff_two_eq_zero (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u * v ≠ 1) (huv' : u * v⁻¹ ≠ 1) :
    addDefectSumCoeff u v 2 = 0 := by
  have h1u : (1 : K) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have h1v : (1 : K) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
  have h1uv : (1 : K) - u * v ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  have h1uv' : (1 : K) - u * v⁻¹ ≠ 0 := sub_ne_zero.mpr (Ne.symm huv')
  have huv0 : u * v ≠ 0 := mul_ne_zero hu0 hv0
  have huv'0 : u * v⁻¹ ≠ 0 := mul_ne_zero hu0 (inv_ne_zero hv0)
  have hune : u ≠ v := fun h => huv' (by rw [h, mul_inv_cancel₀ hv0])
  have hsub : u - v ≠ 0 := sub_ne_zero.mpr hune
  have hsub' : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hune)
  simp only [addDefectSumCoeff, cauchyMul_two, cauchyMul_one, cauchyMul_zero, xCoeffFull_zero,
    xCoeffFull_one, xCoeffFull_two, a₄Coeff_zero, a₆Coeff_zero, a₄Coeff_one, a₆Coeff_one,
    a₄Coeff_two, a₆Coeff_two, xfun, zero_mul, mul_zero, zero_add, add_zero]
  field_simp
  ring

end Warmups

section ZeroRow

variable (K)

def SumDefectCoeffVanishing : Prop :=
  ∀ q u v : K, ExpansionRegion q u v → ∀ M : ℕ, addDefectSumCoeff u v M = 0

variable {K}

theorem symAdd_sum_of_vanishing (hvan : SumDefectCoeffVanishing K)
    (hreg : ExpansionRegion q u v) :
    (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v) := by
  refine symAdd_sum_of_coeff_eq (B := 0) (s := fun _ _ => (∅ : Finset ℤ))
    (a := fun _ _ _ => (0 : K)) le_rfl (fun M k j => by simp) (fun q' u' v' hreg' M => ?_) hreg
  rw [hvan q' u' v' hreg' M]
  simp

end ZeroRow

end TateCurve

set_option autoImplicit false

set_option linter.unusedSectionVars false

open scoped NNReal
open IsUltrametricDist Filter
open WeierstrassCurve.Affine

namespace TateCurve
p2m_export "TateCurve" "eq_zero_of_master_rows unitSpectator norm_unitSpectator unitSpectator_ne_one spectatorRows norm_spectatorRows_le symAdd_sum_of_laurentRows symAdd_prod_of_laurentRows symSumNum symProdNum OffLattice OffLattice.zpow_mul OffLattice.inv AddParams AddParams.swap pointX_inv_mul pointX_inv_mul_inv pointX_q_inv_mul addDefectSum addDefectProd addDefectSum_q_mul_left addDefectProd_q_mul_left nodal_symSum offLattice_of_norm_eq_one addParams_of_norm_one_spectator norm_mul_eq_of_norm_eq_one norm_mul_inv_eq_of_norm_eq_one specTail specAlpha specGamma summable_specTail_term norm_specTail_le spec_eq_zero_of_master summable_norm_a₄Series summable_norm_a₆Series summable_norm_xSeries summable_norm_ySeries ne_zero_of_one_lt_norm norm_q_lt_one_of_qshift norm_inv_lt_one_of_one_lt_norm cauchyMul_two tent xfun_mul_Fz_eq_tent cauchyMul cauchyMul_zero cauchyMul_one qSeries_mul summable_norm_cauchyMul xCoeffFull xCoeffFull_zero xCoeffFull_succ yCoeffFull yCoeffFull_zero yCoeffFull_succ a₄Coeff a₄Coeff_zero a₄Coeff_succ a₆Coeff a₆Coeff_zero a₆Coeff_succ xfun yfun pointX pointY term term_zero summable_term coeffSum b a₄ a₆ curve curve_a₁ curve_a₃ xDivTerm yDivTerm xCoeff yCoeff pointX_inv pointX_q_mul pointX_zpow_mul pointPsiTwo addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff psiCoeffFull addDefectDiffCoeff LatticeRep OnHalfLattice MuTranslation pointX_qExpansion pointY_qExpansion pointY_q_mul pointY_inv pointY_zpow_mul"
p2m_open "TateCurve~tsum_succ_prod_eq_tsum_divisors"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

section PsiTwo

variable [CompleteSpace K] {q w : K}
lemma pointPsiTwo_def : pointPsiTwo q w = 2 * pointY q w + pointX q w := rfl

lemma pointPsiTwo_q_mul (hq0 : q ≠ 0) : pointPsiTwo q (q * w) = pointPsiTwo q w := by
  unfold pointPsiTwo
  rw [pointX_q_mul hq0, pointY_q_mul hq0]

lemma pointPsiTwo_zpow_mul (hq0 : q ≠ 0) (n : ℤ) :
    pointPsiTwo q (q ^ n * w) = pointPsiTwo q w := by
  unfold pointPsiTwo
  rw [pointX_zpow_mul hq0, pointY_zpow_mul hq0]

lemma pointPsiTwo_inv (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hw0 : w ≠ 0) (hw : OffLattice q w) :
    pointPsiTwo q w⁻¹ = -pointPsiTwo q w := by
  unfold pointPsiTwo
  rw [pointX_inv hq0 hw0 hw, pointY_inv hq0 hq hw0 hw]
  ring

lemma sub_negY_curve (q x y : K) : y - (curve q).toAffine.negY x y = 2 * y + x := by
  rw [negY]
  show y - (-y - (curve q).a₁ * x - (curve q).a₃) = 2 * y + x
  rw [curve_a₁, curve_a₃]
  ring

lemma pointPsiTwo_eq_sub_negY :
    pointPsiTwo q w = pointY q w - (curve q).toAffine.negY (pointX q w) (pointY q w) := by
  rw [pointPsiTwo_def, sub_negY_curve]

end PsiTwo

section Defect

variable [CompleteSpace K] {q u v : K}

variable (q u v)
variable {q u v}

lemma addDefectDiff_eq_zero_iff :
    addDefectDiff q u v = 0 ↔
      (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        -(pointPsiTwo q u * pointPsiTwo q v) := by
  unfold addDefectDiff
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

lemma addDefectDiff_eq_zero_iff' :
    addDefectDiff q u v = 0 ↔
      (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)) := by
  unfold addDefectDiff pointPsiTwo
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

lemma addDefectDiff_eq_zero_iff_curve :
    addDefectDiff q u v = 0 ↔
      (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        -((pointY q u - (curve q).toAffine.negY (pointX q u) (pointY q u)) *
          (pointY q v - (curve q).toAffine.negY (pointX q v) (pointY q v))) := by
  rw [addDefectDiff_eq_zero_iff, pointPsiTwo_eq_sub_negY, pointPsiTwo_eq_sub_negY]

theorem addDefectDiff_q_mul_left (hq0 : q ≠ 0) :
    addDefectDiff q (q * u) v = addDefectDiff q u v := by
  unfold addDefectDiff
  rw [mul_assoc q u v, mul_assoc q u v⁻¹, pointX_q_mul hq0, pointX_q_mul hq0,
    pointX_q_mul hq0, pointPsiTwo_q_mul hq0]

theorem addDefectDiff_q_mul_right (hq0 : q ≠ 0) :
    addDefectDiff q u (q * v) = addDefectDiff q u v := by
  unfold addDefectDiff
  rw [show u * (q * v) = q * (u * v) by ring,
    show u * (q * v)⁻¹ = q⁻¹ * (u * v⁻¹) by rw [mul_inv_rev]; ring,
    pointX_q_mul hq0, pointX_q_inv_mul hq0, pointX_q_mul hq0, pointPsiTwo_q_mul hq0]

theorem addDefectDiff_swap (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hdiv : OffLattice q (u * v⁻¹)) :
    addDefectDiff q v u = addDefectDiff q u v := by
  unfold addDefectDiff
  rw [mul_comm v u, show v * u⁻¹ = (u * v⁻¹)⁻¹ by rw [mul_inv_rev, inv_inv],
    pointX_inv hq0 (mul_ne_zero hu0 (inv_ne_zero hv0)) hdiv]
  ring

theorem addDefectDiff_inv_left (hq : ‖q‖₊ < 1) (h : AddParams q u v) :
    addDefectDiff q u⁻¹ v = -addDefectDiff q u v := by
  unfold addDefectDiff
  rw [pointX_inv_mul h.q_ne_zero h.u_ne_zero h.v_ne_zero h.offLattice_div,
    pointX_inv_mul_inv h.q_ne_zero h.u_ne_zero h.v_ne_zero h.offLattice_mul,
    pointX_inv h.q_ne_zero h.u_ne_zero h.offLattice_u,
    pointPsiTwo_inv h.q_ne_zero hq h.u_ne_zero h.offLattice_u]
  ring

theorem addDefectDiff_inv_right (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hv0 : v ≠ 0)
    (hv : OffLattice q v) :
    addDefectDiff q u v⁻¹ = -addDefectDiff q u v := by
  unfold addDefectDiff
  rw [inv_inv, pointX_inv hq0 hv0 hv, pointPsiTwo_inv hq0 hq hv0 hv]
  ring

end Defect

section Nodal

variable {u v : K}

theorem nodal_symDiff (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u * v ≠ 1) (huv' : u * v⁻¹ ≠ 1) :
    (xfun (u * v) - xfun (u * v⁻¹)) * (xfun u - xfun v) ^ 2 =
      -((2 * yfun u + xfun u) * (2 * yfun v + xfun v)) := by
  have h1u : (1 : K) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have h1v : (1 : K) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
  have h1uv : (1 : K) - u * v ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  have h1uv' : (1 : K) - u * v⁻¹ ≠ 0 := sub_ne_zero.mpr (Ne.symm huv')
  have hne : u ≠ v := by
    intro h
    exact huv' (by rw [h, mul_inv_cancel₀ hv0])
  have hsub : u - v ≠ 0 := sub_ne_zero.mpr hne
  have hsub' : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  unfold xfun yfun
  field_simp
  ring

end Nodal

end TateCurve

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "eq_zero_of_master_rows unitSpectator norm_unitSpectator unitSpectator_ne_one spectatorRows norm_spectatorRows_le symAdd_sum_of_laurentRows symAdd_prod_of_laurentRows symSumNum symProdNum OffLattice OffLattice.zpow_mul OffLattice.inv AddParams AddParams.swap pointX_inv_mul pointX_inv_mul_inv pointX_q_inv_mul addDefectSum addDefectProd addDefectSum_q_mul_left addDefectProd_q_mul_left nodal_symSum offLattice_of_norm_eq_one addParams_of_norm_one_spectator norm_mul_eq_of_norm_eq_one norm_mul_inv_eq_of_norm_eq_one specTail specAlpha specGamma summable_specTail_term norm_specTail_le spec_eq_zero_of_master summable_norm_a₄Series summable_norm_a₆Series summable_norm_xSeries summable_norm_ySeries ne_zero_of_one_lt_norm norm_q_lt_one_of_qshift norm_inv_lt_one_of_one_lt_norm cauchyMul_two tent xfun_mul_Fz_eq_tent cauchyMul cauchyMul_zero cauchyMul_one qSeries_mul summable_norm_cauchyMul xCoeffFull xCoeffFull_zero xCoeffFull_succ yCoeffFull yCoeffFull_zero yCoeffFull_succ a₄Coeff a₄Coeff_zero a₄Coeff_succ a₆Coeff a₆Coeff_zero a₆Coeff_succ xfun yfun pointX pointY term term_zero summable_term coeffSum b a₄ a₆ curve curve_a₁ curve_a₃ xDivTerm yDivTerm xCoeff yCoeff pointX_inv pointX_q_mul pointX_zpow_mul pointPsiTwo addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff psiCoeffFull addDefectDiffCoeff LatticeRep OnHalfLattice MuTranslation pointX_qExpansion pointY_qExpansion pointY_q_mul pointY_inv pointY_zpow_mul"
p2m_open "TateCurve~tsum_succ_prod_eq_tsum_divisors"

open scoped NNReal

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q u v : K}

section Helpers

private lemma nnnorm_lt_one_of_norm_lt_one_DE {x : K} (h : ‖x‖ < 1) : ‖x‖₊ < 1 := by
  exact_mod_cast h

private lemma region_nnnorm_pair_DE {w : K} (hq0 : q ≠ 0) (hlo : ‖q‖ < ‖w‖)
    (hhi : ‖q‖ * ‖w‖ < 1) : ‖q * w‖₊ < 1 ∧ ‖q * w⁻¹‖₊ < 1 := by
  have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hwpos : (0 : ℝ) < ‖w‖ := lt_trans hqpos hlo
  constructor
  · have h1 : ‖q * w‖ < 1 := by rw [norm_mul]; exact hhi
    exact nnnorm_lt_one_of_norm_lt_one_DE h1
  · have h2 : ‖q * w⁻¹‖ < 1 := by
      rw [norm_mul, norm_inv, ← div_eq_mul_inv]
      exact (div_lt_one hwpos).mpr hlo
    exact nnnorm_lt_one_of_norm_lt_one_DE h2

private lemma hasSum_of_eq_tsum_DE {c : ℕ → K} {x : K}
    (hn : Summable fun N => ‖c N * q ^ N‖) (hx : x = ∑' N : ℕ, c N * q ^ N) :
    HasSum (fun N => c N * q ^ N) x := by
  rw [hx]; exact hn.of_norm.hasSum

private lemma hasSum_qSeries_mul_DE {c d : ℕ → K} {x y : K}
    (hc : Summable fun N => ‖c N * q ^ N‖) (hd : Summable fun N => ‖d N * q ^ N‖)
    (hx : HasSum (fun N => c N * q ^ N) x) (hy : HasSum (fun N => d N * q ^ N) y) :
    HasSum (fun N => cauchyMul c d N * q ^ N) (x * y) := by
  have hval : x * y = ∑' N : ℕ, cauchyMul c d N * q ^ N := by
    rw [← hx.tsum_eq, ← hy.tsum_eq]
    exact qSeries_mul hc hd
  rw [hval]
  exact ((summable_norm_cauchyMul hc hd).of_norm).hasSum

private lemma hasSum_congr_fun_DE {f g : ℕ → K} {x : K} (h : HasSum f x)
    (heq : ∀ N, g N = f N) : HasSum g x := by
  have hfg : g = f := funext heq
  rw [hfg]; exact h

end Helpers

section PsiCoeff
@[scoped simp] theorem psiCoeffFull_zero : psiCoeffFull u 0 = 2 * yfun u + xfun u := by
  simp [psiCoeffFull]

@[scoped simp] theorem psiCoeffFull_succ (N : ℕ) :
    psiCoeffFull u (N + 1) = 2 * yCoeff u (N + 1) + xCoeff u (N + 1) := by
  simp [psiCoeffFull]

theorem two_yDivTerm_add_xDivTerm (d : ℕ) :
    2 * yDivTerm u d + xDivTerm u d = (d : K) ^ 2 * (u ^ d - u⁻¹ ^ d) := by
  rcases d with _ | k
  · simp [yDivTerm, xDivTerm]
  · have hdvd : 2 ∣ (k + 1) * k := by
      simpa [mul_comm] using (Nat.even_mul_succ_self k).two_dvd
    have hn : 2 * (k + 1).choose 2 = (k + 1) * k := by
      rw [Nat.choose_two_right, Nat.succ_sub_one, Nat.mul_div_cancel' hdvd]
    have hn2 : 2 * (k + 1).choose 2 + (k + 1) = (k + 1) * (k + 1) := by rw [hn]; ring
    have h2c := congrArg (fun n : ℕ => (n : K)) hn2
    push_cast at h2c
    unfold yDivTerm xDivTerm
    push_cast
    linear_combination (u ^ (k + 1) - u⁻¹ ^ (k + 1)) * h2c

theorem psiCoeffFull_succ_eq_divisorSum (N : ℕ) :
    psiCoeffFull u (N + 1) = ∑ d ∈ (N + 1).divisors, (d : K) ^ 2 * (u ^ d - u⁻¹ ^ d) := by
  rw [psiCoeffFull_succ]
  unfold yCoeff xCoeff
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => two_yDivTerm_add_xDivTerm d

theorem summable_norm_psiSeries (hq : ‖q‖₊ < 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) :
    Summable fun N => ‖psiCoeffFull u N * q ^ N‖ := by
  have hY := summable_norm_ySeries (q := q) (u := u) hq hqu hqu'
  have hX := summable_norm_xSeries (q := q) (u := u) hq hqu hqu'
  refine Summable.of_nonneg_of_le (fun N => norm_nonneg _) (fun N => ?_)
    ((hY.mul_left ‖(2 : K)‖).add hX)
  have hsplit : psiCoeffFull u N * q ^ N
      = 2 * (yCoeffFull u N * q ^ N) + xCoeffFull u N * q ^ N := by
    simp only [psiCoeffFull]; ring
  rw [hsplit]
  calc ‖2 * (yCoeffFull u N * q ^ N) + xCoeffFull u N * q ^ N‖
      ≤ ‖2 * (yCoeffFull u N * q ^ N)‖ + ‖xCoeffFull u N * q ^ N‖ := norm_add_le _ _
    _ = ‖(2 : K)‖ * ‖yCoeffFull u N * q ^ N‖ + ‖xCoeffFull u N * q ^ N‖ := by rw [norm_mul]

theorem hasSum_psiSeries (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : OffLattice q u) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) :
    HasSum (fun N => psiCoeffFull u N * q ^ N) (pointPsiTwo q u) := by
  have nY := summable_norm_ySeries (q := q) (u := u) hq hqu hqu'
  have nX := summable_norm_xSeries (q := q) (u := u) hq hqu hqu'
  have hY : HasSum (fun N => yCoeffFull u N * q ^ N) (pointY q u) :=
    hasSum_of_eq_tsum_DE nY (pointY_eq_tsum hq0 hq hu0 hu hqu hqu')
  have hX : HasSum (fun N => xCoeffFull u N * q ^ N) (pointX q u) :=
    hasSum_of_eq_tsum_DE nX (pointX_eq_tsum hq0 hq hu0 hu hqu hqu')
  have h := (hY.mul_left 2).add hX
  rw [pointPsiTwo_def]
  exact hasSum_congr_fun_DE h fun N => by simp only [psiCoeffFull]; ring

end PsiCoeff

section Coefficients

theorem addDefectDiffCoeff_zero (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u * v ≠ 1) (huv' : u * v⁻¹ ≠ 1) :
    addDefectDiffCoeff u v 0 = 0 := by
  have hnodal := nodal_symDiff (K := K) hu0 hv0 hu1 hv1 huv huv'
  simp only [addDefectDiffCoeff, cauchyMul_zero, xCoeffFull_zero, psiCoeffFull_zero]
  linear_combination hnodal

end Coefficients

section Expansion

set_option maxHeartbeats 3200000 in

theorem addDefectDiff_qExpansion (hreg : ExpansionRegion q u v) :
    HasSum (fun N : ℕ => addDefectDiffCoeff u v N * q ^ N) (addDefectDiff q u v) := by

  have hq0 : q ≠ 0 := hreg.params.q_ne_zero
  have hu0 : u ≠ 0 := hreg.params.u_ne_zero
  have hv0 : v ≠ 0 := hreg.params.v_ne_zero
  have hm0 : u * v ≠ 0 := mul_ne_zero hu0 hv0
  have hd0 : u * v⁻¹ ≠ 0 := mul_ne_zero hu0 (inv_ne_zero hv0)
  have hq1 : ‖q‖₊ < 1 := nnnorm_lt_one_of_norm_lt_one_DE hreg.norm_q_lt_one
  obtain ⟨hqu, hqu'⟩ := region_nnnorm_pair_DE hq0 hreg.u_lo hreg.u_hi
  obtain ⟨hqv, hqv'⟩ := region_nnnorm_pair_DE hq0 hreg.v_lo hreg.v_hi
  obtain ⟨hqm, hqm'⟩ := region_nnnorm_pair_DE hq0 hreg.mul_lo hreg.mul_hi
  obtain ⟨hqd, hqd'⟩ := region_nnnorm_pair_DE hq0 hreg.div_lo hreg.div_hi

  have nP : Summable fun N => ‖xCoeffFull u N * q ^ N‖ := summable_norm_xSeries hq1 hqu hqu'
  have nQ : Summable fun N => ‖xCoeffFull v N * q ^ N‖ := summable_norm_xSeries hq1 hqv hqv'
  have nM : Summable fun N => ‖xCoeffFull (u * v) N * q ^ N‖ :=
    summable_norm_xSeries hq1 hqm hqm'
  have nD : Summable fun N => ‖xCoeffFull (u * v⁻¹) N * q ^ N‖ :=
    summable_norm_xSeries hq1 hqd hqd'
  have nPsiU : Summable fun N => ‖psiCoeffFull u N * q ^ N‖ :=
    summable_norm_psiSeries hq1 hqu hqu'
  have nPsiV : Summable fun N => ‖psiCoeffFull v N * q ^ N‖ :=
    summable_norm_psiSeries hq1 hqv hqv'

  have hXu : HasSum (fun N => xCoeffFull u N * q ^ N) (pointX q u) :=
    hasSum_of_eq_tsum_DE nP
      (pointX_eq_tsum hq0 hq1 hu0 hreg.params.offLattice_u hqu hqu')
  have hXv : HasSum (fun N => xCoeffFull v N * q ^ N) (pointX q v) :=
    hasSum_of_eq_tsum_DE nQ
      (pointX_eq_tsum hq0 hq1 hv0 hreg.params.offLattice_v hqv hqv')
  have hXm : HasSum (fun N => xCoeffFull (u * v) N * q ^ N) (pointX q (u * v)) :=
    hasSum_of_eq_tsum_DE nM
      (pointX_eq_tsum hq0 hq1 hm0 hreg.params.offLattice_mul hqm hqm')
  have hXd : HasSum (fun N => xCoeffFull (u * v⁻¹) N * q ^ N) (pointX q (u * v⁻¹)) :=
    hasSum_of_eq_tsum_DE nD
      (pointX_eq_tsum hq0 hq1 hd0 hreg.params.offLattice_div hqd hqd')
  have hPsiU : HasSum (fun N => psiCoeffFull u N * q ^ N) (pointPsiTwo q u) :=
    hasSum_psiSeries hq0 hq1 hu0 hreg.params.offLattice_u hqu hqu'
  have hPsiV : HasSum (fun N => psiCoeffFull v N * q ^ N) (pointPsiTwo q v) :=
    hasSum_psiSeries hq0 hq1 hv0 hreg.params.offLattice_v hqv hqv'

  have nPP := summable_norm_cauchyMul nP nP
  have nPQ := summable_norm_cauchyMul nP nQ
  have nQQ := summable_norm_cauchyMul nQ nQ
  have hPP := hasSum_qSeries_mul_DE nP nP hXu hXu
  have hPQ := hasSum_qSeries_mul_DE nP nQ hXu hXv
  have hQQ := hasSum_qSeries_mul_DE nQ nQ hXv hXv

  have H1 := hasSum_qSeries_mul_DE nM nPP hXm hPP
  have H2 := hasSum_qSeries_mul_DE nM nPQ hXm hPQ
  have H3 := hasSum_qSeries_mul_DE nM nQQ hXm hQQ
  have H4 := hasSum_qSeries_mul_DE nD nPP hXd hPP
  have H5 := hasSum_qSeries_mul_DE nD nPQ hXd hPQ
  have H6 := hasSum_qSeries_mul_DE nD nQQ hXd hQQ
  have H7 := hasSum_qSeries_mul_DE nPsiU nPsiV hPsiU hPsiV

  have S1 := H1.sub (H2.mul_left 2)
  have S2 := S1.add H3
  have S3 := S2.sub H4
  have S4 := S3.add (H5.mul_left 2)
  have S5 := S4.sub H6
  have Hbig := S5.add H7
  have hdefect : addDefectDiff q u v
      = pointX q (u * v) * (pointX q u * pointX q u)
        - 2 * (pointX q (u * v) * (pointX q u * pointX q v))
        + pointX q (u * v) * (pointX q v * pointX q v)
        - pointX q (u * v⁻¹) * (pointX q u * pointX q u)
        + 2 * (pointX q (u * v⁻¹) * (pointX q u * pointX q v))
        - pointX q (u * v⁻¹) * (pointX q v * pointX q v)
        + pointPsiTwo q u * pointPsiTwo q v := by
    simp only [addDefectDiff]
    ring
  rw [hdefect]
  exact hasSum_congr_fun_DE Hbig fun N => by
    simp only [addDefectDiffCoeff]
    ring

end Expansion

section Bridge

theorem diffExpansion_of_coeff_eq {f : K → K → ℕ → K}
    (hcoeff : ∀ q' u' v' : K, ExpansionRegion q' u' v' → ∀ M : ℕ,
      f u' v' M = addDefectDiffCoeff u' v' M) :
    ∀ q' u' v' : K, ExpansionRegion q' u' v' →
      HasSum (fun M : ℕ => f u' v' M * q' ^ M) (addDefectDiff q' u' v') := by
  intro q' u' v' hreg'
  refine hasSum_congr_fun_DE (addDefectDiff_qExpansion hreg') fun M => ?_
  rw [hcoeff q' u' v' hreg' M]

end Bridge

end TateCurve
p2m_reactivate "P2MW.S_TateCurve_ks17_A_exports.TateCurve"

namespace TateCurve
p2m_export "TateCurve" "eq_zero_of_master_rows unitSpectator norm_unitSpectator unitSpectator_ne_one spectatorRows norm_spectatorRows_le symAdd_sum_of_laurentRows symAdd_prod_of_laurentRows symSumNum symProdNum OffLattice OffLattice.zpow_mul OffLattice.inv AddParams AddParams.swap pointX_inv_mul pointX_inv_mul_inv pointX_q_inv_mul addDefectSum addDefectProd addDefectSum_q_mul_left addDefectProd_q_mul_left nodal_symSum offLattice_of_norm_eq_one addParams_of_norm_one_spectator norm_mul_eq_of_norm_eq_one norm_mul_inv_eq_of_norm_eq_one specTail specAlpha specGamma summable_specTail_term norm_specTail_le spec_eq_zero_of_master summable_norm_a₄Series summable_norm_a₆Series summable_norm_xSeries summable_norm_ySeries ne_zero_of_one_lt_norm norm_q_lt_one_of_qshift norm_inv_lt_one_of_one_lt_norm cauchyMul_two tent xfun_mul_Fz_eq_tent cauchyMul cauchyMul_zero cauchyMul_one qSeries_mul summable_norm_cauchyMul xCoeffFull xCoeffFull_zero xCoeffFull_succ yCoeffFull yCoeffFull_zero yCoeffFull_succ a₄Coeff a₄Coeff_zero a₄Coeff_succ a₆Coeff a₆Coeff_zero a₆Coeff_succ xfun yfun pointX pointY term term_zero summable_term coeffSum b a₄ a₆ curve curve_a₁ curve_a₃ xDivTerm yDivTerm xCoeff yCoeff pointX_inv pointX_q_mul pointX_zpow_mul pointPsiTwo addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff psiCoeffFull addDefectDiffCoeff LatticeRep OnHalfLattice MuTranslation pointX_qExpansion pointY_qExpansion pointY_q_mul pointY_inv pointY_zpow_mul"
p2m_open "TateCurve~tsum_succ_prod_eq_tsum_divisors"
variable {K : Type*} [NontriviallyNormedField K]
section AnnulusTranslateInline
variable {q u : K}
private theorem nnnorm_lt_one_iff_norm_AT {x : K} : ‖x‖₊ < 1 ↔ ‖x‖ < 1 := by
  rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]

theorem exists_zpow_mul_norm_Ioc (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hu0 : u ≠ 0) :
    ∃ n : ℤ, ‖q‖ < ‖q ^ n * u‖ ∧ ‖q ^ n * u‖ ≤ 1 := by
  have hq_pos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hu_pos : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
  have hq_ne : (‖q‖ : ℝ) ≠ 0 := ne_of_gt hq_pos
  have hy : (1 : ℝ) < ‖q‖⁻¹ := one_lt_inv_iff₀.mpr ⟨hq_pos, hq⟩
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hu_pos hy
  have hqk_pos : (0 : ℝ) < ‖q‖ ^ (n + 1 : ℤ) := zpow_pos hq_pos _

  have hcancel : ∀ m : ℤ, ‖q‖⁻¹ ^ m * ‖q‖ ^ m = 1 := fun m => by
    rw [← mul_zpow, inv_mul_cancel₀ hq_ne, one_zpow]
  refine ⟨n + 1, ?_, ?_⟩
  ·
    have hkey : ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ n = ‖q‖ := by
      rw [zpow_add₀ hq_ne, zpow_one]
      calc ‖q‖ ^ n * ‖q‖ * ‖q‖⁻¹ ^ n
          = ‖q‖⁻¹ ^ n * (‖q‖ ^ n * ‖q‖) := mul_comm _ _
        _ = ‖q‖⁻¹ ^ n * ‖q‖ ^ n * ‖q‖ := (mul_assoc _ _ _).symm
        _ = 1 * ‖q‖ := by rw [hcancel n]
        _ = ‖q‖ := one_mul _
    have hlt : ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ n < ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ :=
      mul_lt_mul_of_pos_left hn1 hqk_pos
    rw [norm_mul, norm_zpow]
    calc ‖q‖ = ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ n := hkey.symm
      _ < ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ := hlt
  ·
    have hkey : ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1) = 1 := by
      calc ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1)
          = ‖q‖⁻¹ ^ (n + 1) * ‖q‖ ^ (n + 1) := mul_comm _ _
        _ = 1 := hcancel (n + 1)
    have hle : ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ ≤ ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1) :=
      mul_le_mul_of_nonneg_left hn2 hqk_pos.le
    rw [norm_mul, norm_zpow]
    calc ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ ≤ ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1) := hle
      _ = 1 := hkey

end AnnulusTranslateInline
p2m_reactivate "P2MW.S_TateCurve_ks17_A_exports.TateCurve"
end TateCurve
p2m_reactivate "P2MW.S_TateCurve_ks17_A_exports.TateCurve"

open scoped NNReal

namespace TateCurve
p2m_export "TateCurve" "eq_zero_of_master_rows unitSpectator norm_unitSpectator unitSpectator_ne_one spectatorRows norm_spectatorRows_le symAdd_sum_of_laurentRows symAdd_prod_of_laurentRows symSumNum symProdNum OffLattice OffLattice.zpow_mul OffLattice.inv AddParams AddParams.swap pointX_inv_mul pointX_inv_mul_inv pointX_q_inv_mul addDefectSum addDefectProd addDefectSum_q_mul_left addDefectProd_q_mul_left nodal_symSum offLattice_of_norm_eq_one addParams_of_norm_one_spectator norm_mul_eq_of_norm_eq_one norm_mul_inv_eq_of_norm_eq_one specTail specAlpha specGamma summable_specTail_term norm_specTail_le spec_eq_zero_of_master summable_norm_a₄Series summable_norm_a₆Series summable_norm_xSeries summable_norm_ySeries ne_zero_of_one_lt_norm norm_q_lt_one_of_qshift norm_inv_lt_one_of_one_lt_norm cauchyMul_two tent xfun_mul_Fz_eq_tent cauchyMul cauchyMul_zero cauchyMul_one qSeries_mul summable_norm_cauchyMul xCoeffFull xCoeffFull_zero xCoeffFull_succ yCoeffFull yCoeffFull_zero yCoeffFull_succ a₄Coeff a₄Coeff_zero a₄Coeff_succ a₆Coeff a₆Coeff_zero a₆Coeff_succ xfun yfun pointX pointY term term_zero summable_term coeffSum b a₄ a₆ curve curve_a₁ curve_a₃ xDivTerm yDivTerm xCoeff yCoeff pointX_inv pointX_q_mul pointX_zpow_mul pointPsiTwo addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff psiCoeffFull addDefectDiffCoeff LatticeRep OnHalfLattice MuTranslation pointX_qExpansion pointY_qExpansion pointY_q_mul pointY_inv pointY_zpow_mul"
p2m_open "TateCurve~tsum_succ_prod_eq_tsum_divisors"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q u v w : K}

lemma not_onHalfLattice_of_norm_eq_one (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hw : ‖w‖ = 1) :
    ¬ OnHalfLattice q w := by
  rintro ⟨m, hm⟩
  have ht0 : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hqm : ‖(q : K) ^ m * w‖ = ‖q‖ ^ m := by
    rw [norm_mul, norm_zpow, hw, mul_one]
  rw [hqm, ← zpow_add₀ (ne_of_gt ht0)] at hm

  by_cases hm0 : m ≤ 0
  · have h2 : ‖q‖ ^ (0 : ℤ) ≤ ‖q‖ ^ (m + m) :=
      zpow_le_zpow_right_of_le_one₀ ht0 hq.le (by omega)
    rw [zpow_zero, hm] at h2
    linarith
  · have h2 : ‖q‖ ^ (m + m) ≤ ‖q‖ ^ (2 : ℤ) :=
      zpow_le_zpow_right_of_le_one₀ ht0 hq.le (by omega)
    have h3 : ‖q‖ ^ (2 : ℤ) = ‖q‖ * ‖q‖ := by
      rw [show (2 : ℤ) = 1 + 1 by norm_num, zpow_add₀ (ne_of_gt ht0), zpow_one]
    have h4 : ‖q‖ * ‖q‖ < ‖q‖ * 1 := mul_lt_mul_of_pos_left hq ht0
    rw [hm, h3] at h2
    rw [mul_one] at h4
    linarith

private lemma prod_form_RE (hq0 : q ≠ 0) (m n : ℤ) (a b : K) :
    (q ^ m * a) * (q ^ n * b) = q ^ (m + n) * (a * b) := by
  rw [zpow_add₀ hq0]; ring

private lemma inv_form_RE (hq0 : q ≠ 0) (n : ℤ) (b : K) :
    (q ^ n * b)⁻¹ = q ^ (-n) * b⁻¹ := by
  rw [mul_inv, zpow_neg]

namespace AddParams
p2m_open_scoped "TateCurve.AddParams" in

private lemma _root_.TateCurve.AddParams.latticeRep {u' v' : K} (hp : AddParams q u v)
    (hu' : LatticeRep q u u') (hv' : LatticeRep q v v') : AddParams q u' v' := by
  have hq0 : q ≠ 0 := hp.q_ne_zero
  obtain ⟨m, hm⟩ := hu'
  obtain ⟨n, hn⟩ := hv'
  have hmulinv : u⁻¹ * v = (u * v⁻¹)⁻¹ := by rw [mul_inv, inv_inv]
  have hdivinv : u⁻¹ * v⁻¹ = (u * v)⁻¹ := (mul_inv u v).symm
  rcases hm with hm | hm <;> rcases hn with hn | hn <;> subst hm <;> subst hn
  · exact
      { q_ne_zero := hq0
        u_ne_zero := mul_ne_zero (zpow_ne_zero m hq0) hp.u_ne_zero
        v_ne_zero := mul_ne_zero (zpow_ne_zero n hq0) hp.v_ne_zero
        offLattice_u := OffLattice.zpow_mul hq0 m hp.offLattice_u
        offLattice_v := OffLattice.zpow_mul hq0 n hp.offLattice_v
        offLattice_mul := by
          rw [prod_form_RE hq0]
          exact OffLattice.zpow_mul hq0 (m + n) hp.offLattice_mul
        offLattice_div := by
          rw [inv_form_RE hq0, prod_form_RE hq0]
          exact OffLattice.zpow_mul hq0 (m + -n) hp.offLattice_div }
  · exact
      { q_ne_zero := hq0
        u_ne_zero := mul_ne_zero (zpow_ne_zero m hq0) hp.u_ne_zero
        v_ne_zero := mul_ne_zero (zpow_ne_zero n hq0) (inv_ne_zero hp.v_ne_zero)
        offLattice_u := OffLattice.zpow_mul hq0 m hp.offLattice_u
        offLattice_v := OffLattice.zpow_mul hq0 n (OffLattice.inv hq0 hp.offLattice_v)
        offLattice_mul := by
          rw [prod_form_RE hq0]
          exact OffLattice.zpow_mul hq0 (m + n) hp.offLattice_div
        offLattice_div := by
          rw [inv_form_RE hq0, prod_form_RE hq0, inv_inv]
          exact OffLattice.zpow_mul hq0 (m + -n) hp.offLattice_mul }
  · exact
      { q_ne_zero := hq0
        u_ne_zero := mul_ne_zero (zpow_ne_zero m hq0) (inv_ne_zero hp.u_ne_zero)
        v_ne_zero := mul_ne_zero (zpow_ne_zero n hq0) hp.v_ne_zero
        offLattice_u := OffLattice.zpow_mul hq0 m (OffLattice.inv hq0 hp.offLattice_u)
        offLattice_v := OffLattice.zpow_mul hq0 n hp.offLattice_v
        offLattice_mul := by
          rw [prod_form_RE hq0, hmulinv]
          exact OffLattice.zpow_mul hq0 (m + n) (OffLattice.inv hq0 hp.offLattice_div)
        offLattice_div := by
          rw [inv_form_RE hq0, prod_form_RE hq0, hdivinv]
          exact OffLattice.zpow_mul hq0 (m + -n) (OffLattice.inv hq0 hp.offLattice_mul) }
  · exact
      { q_ne_zero := hq0
        u_ne_zero := mul_ne_zero (zpow_ne_zero m hq0) (inv_ne_zero hp.u_ne_zero)
        v_ne_zero := mul_ne_zero (zpow_ne_zero n hq0) (inv_ne_zero hp.v_ne_zero)
        offLattice_u := OffLattice.zpow_mul hq0 m (OffLattice.inv hq0 hp.offLattice_u)
        offLattice_v := OffLattice.zpow_mul hq0 n (OffLattice.inv hq0 hp.offLattice_v)
        offLattice_mul := by
          rw [prod_form_RE hq0, hdivinv]
          exact OffLattice.zpow_mul hq0 (m + n) (OffLattice.inv hq0 hp.offLattice_mul)
        offLattice_div := by
          rw [inv_form_RE hq0, prod_form_RE hq0, inv_inv, hmulinv]
          exact OffLattice.zpow_mul hq0 (m + -n) (OffLattice.inv hq0 hp.offLattice_div) }

end AddParams
p2m_export "TateCurve" "AddParams.latticeRep"

private lemma transport_core_RE (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hp : AddParams q u v)
    {u' v' : K} (hu' : LatticeRep q u u') (hv' : LatticeRep q v v') :
    pointX q u' = pointX q u ∧ pointX q v' = pointX q v ∧
      ((pointX q (u' * v') = pointX q (u * v) ∧
          pointX q (u' * v'⁻¹) = pointX q (u * v⁻¹) ∧
          (2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v') =
            (2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)) ∨
        (pointX q (u' * v') = pointX q (u * v⁻¹) ∧
          pointX q (u' * v'⁻¹) = pointX q (u * v) ∧
          (2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v') =
            -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)))) := by
  have hu0 : u ≠ 0 := hp.u_ne_zero
  have hv0 : v ≠ 0 := hp.v_ne_zero
  have hmul0 : u * v ≠ 0 := mul_ne_zero hu0 hv0
  have hdiv0 : u * v⁻¹ ≠ 0 := mul_ne_zero hu0 (inv_ne_zero hv0)
  have hmulinv : u⁻¹ * v = (u * v⁻¹)⁻¹ := by rw [mul_inv, inv_inv]
  have hdivinv : u⁻¹ * v⁻¹ = (u * v)⁻¹ := (mul_inv u v).symm
  obtain ⟨m, hm⟩ := hu'
  obtain ⟨n, hn⟩ := hv'
  rcases hm with hm | hm <;> rcases hn with hn | hn <;> subst hm <;> subst hn
  ·
    have hXu : pointX q (q ^ m * u) = pointX q u := pointX_zpow_mul hq0 m
    have hXv : pointX q (q ^ n * v) = pointX q v := pointX_zpow_mul hq0 n
    have hXmul : pointX q ((q ^ m * u) * (q ^ n * v)) = pointX q (u * v) := by
      rw [prod_form_RE hq0]; exact pointX_zpow_mul hq0 (m + n)
    have hXdiv : pointX q ((q ^ m * u) * (q ^ n * v)⁻¹) = pointX q (u * v⁻¹) := by
      rw [inv_form_RE hq0, prod_form_RE hq0]; exact pointX_zpow_mul hq0 (m + -n)
    have hpsiu : 2 * pointY q (q ^ m * u) + pointX q (q ^ m * u) =
        2 * pointY q u + pointX q u := by
      rw [pointX_zpow_mul hq0, pointY_zpow_mul hq0]
    have hpsiv : 2 * pointY q (q ^ n * v) + pointX q (q ^ n * v) =
        2 * pointY q v + pointX q v := by
      rw [pointX_zpow_mul hq0, pointY_zpow_mul hq0]
    exact ⟨hXu, hXv, Or.inl ⟨hXmul, hXdiv, by rw [hpsiu, hpsiv]⟩⟩
  ·
    have hXu : pointX q (q ^ m * u) = pointX q u := pointX_zpow_mul hq0 m
    have hXv : pointX q (q ^ n * v⁻¹) = pointX q v := by
      rw [pointX_zpow_mul hq0, pointX_inv hq0 hv0 hp.offLattice_v]
    have hXmul : pointX q ((q ^ m * u) * (q ^ n * v⁻¹)) = pointX q (u * v⁻¹) := by
      rw [prod_form_RE hq0]; exact pointX_zpow_mul hq0 (m + n)
    have hXdiv : pointX q ((q ^ m * u) * (q ^ n * v⁻¹)⁻¹) = pointX q (u * v) := by
      rw [inv_form_RE hq0, prod_form_RE hq0, inv_inv]; exact pointX_zpow_mul hq0 (m + -n)
    have hpsiu : 2 * pointY q (q ^ m * u) + pointX q (q ^ m * u) =
        2 * pointY q u + pointX q u := by
      rw [pointX_zpow_mul hq0, pointY_zpow_mul hq0]
    have hpsiv : 2 * pointY q (q ^ n * v⁻¹) + pointX q (q ^ n * v⁻¹) =
        -(2 * pointY q v + pointX q v) := by
      rw [pointX_zpow_mul hq0, pointY_zpow_mul hq0,
        pointX_inv hq0 hv0 hp.offLattice_v, pointY_inv hq0 hq hv0 hp.offLattice_v]
      ring
    refine ⟨hXu, hXv, Or.inr ⟨hXmul, hXdiv, ?_⟩⟩
    rw [hpsiu, hpsiv]; ring
  ·
    have hXu : pointX q (q ^ m * u⁻¹) = pointX q u := by
      rw [pointX_zpow_mul hq0, pointX_inv hq0 hu0 hp.offLattice_u]
    have hXv : pointX q (q ^ n * v) = pointX q v := pointX_zpow_mul hq0 n
    have hXmul : pointX q ((q ^ m * u⁻¹) * (q ^ n * v)) = pointX q (u * v⁻¹) := by
      rw [prod_form_RE hq0, hmulinv, pointX_zpow_mul hq0,
        pointX_inv hq0 hdiv0 hp.offLattice_div]
    have hXdiv : pointX q ((q ^ m * u⁻¹) * (q ^ n * v)⁻¹) = pointX q (u * v) := by
      rw [inv_form_RE hq0, prod_form_RE hq0, hdivinv, pointX_zpow_mul hq0,
        pointX_inv hq0 hmul0 hp.offLattice_mul]
    have hpsiu : 2 * pointY q (q ^ m * u⁻¹) + pointX q (q ^ m * u⁻¹) =
        -(2 * pointY q u + pointX q u) := by
      rw [pointX_zpow_mul hq0, pointY_zpow_mul hq0,
        pointX_inv hq0 hu0 hp.offLattice_u, pointY_inv hq0 hq hu0 hp.offLattice_u]
      ring
    have hpsiv : 2 * pointY q (q ^ n * v) + pointX q (q ^ n * v) =
        2 * pointY q v + pointX q v := by
      rw [pointX_zpow_mul hq0, pointY_zpow_mul hq0]
    refine ⟨hXu, hXv, Or.inr ⟨hXmul, hXdiv, ?_⟩⟩
    rw [hpsiu, hpsiv]; ring
  ·
    have hXu : pointX q (q ^ m * u⁻¹) = pointX q u := by
      rw [pointX_zpow_mul hq0, pointX_inv hq0 hu0 hp.offLattice_u]
    have hXv : pointX q (q ^ n * v⁻¹) = pointX q v := by
      rw [pointX_zpow_mul hq0, pointX_inv hq0 hv0 hp.offLattice_v]
    have hXmul : pointX q ((q ^ m * u⁻¹) * (q ^ n * v⁻¹)) = pointX q (u * v) := by
      rw [prod_form_RE hq0, hdivinv, pointX_zpow_mul hq0,
        pointX_inv hq0 hmul0 hp.offLattice_mul]
    have hXdiv : pointX q ((q ^ m * u⁻¹) * (q ^ n * v⁻¹)⁻¹) = pointX q (u * v⁻¹) := by
      rw [inv_form_RE hq0, prod_form_RE hq0, inv_inv, hmulinv, pointX_zpow_mul hq0,
        pointX_inv hq0 hdiv0 hp.offLattice_div]
    have hpsiu : 2 * pointY q (q ^ m * u⁻¹) + pointX q (q ^ m * u⁻¹) =
        -(2 * pointY q u + pointX q u) := by
      rw [pointX_zpow_mul hq0, pointY_zpow_mul hq0,
        pointX_inv hq0 hu0 hp.offLattice_u, pointY_inv hq0 hq hu0 hp.offLattice_u]
      ring
    have hpsiv : 2 * pointY q (q ^ n * v⁻¹) + pointX q (q ^ n * v⁻¹) =
        -(2 * pointY q v + pointX q v) := by
      rw [pointX_zpow_mul hq0, pointY_zpow_mul hq0,
        pointX_inv hq0 hv0 hp.offLattice_v, pointY_inv hq0 hq hv0 hp.offLattice_v]
      ring
    refine ⟨hXu, hXv, Or.inl ⟨hXmul, hXdiv, ?_⟩⟩
    rw [hpsiu, hpsiv]; ring

theorem symAdd_sum_of_region_latticeRep (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hreg : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hp : AddParams q u v)
    (hrep : ∃ u' v' : K, LatticeRep q u u' ∧ LatticeRep q v v' ∧ ExpansionRegion q u' v') :
    (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v) := by
  obtain ⟨u', v', hu', hv', hR⟩ := hrep
  have hq' : ‖q‖₊ < 1 := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]; exact hq
  obtain ⟨hXu, hXv, hcase⟩ := transport_core_RE hq0 hq' hp hu' hv'
  have hS1 := hreg u' v' hR
  rcases hcase with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> rw [h1, h2, hXu, hXv] at hS1 <;>
    linear_combination hS1

theorem diff_identity_of_region_latticeRep (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hreg : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v')))
    (hp : AddParams q u v)
    (hrep : ∃ u' v' : K, LatticeRep q u u' ∧ LatticeRep q v v' ∧ ExpansionRegion q u' v') :
    (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)) := by
  obtain ⟨u', v', hu', hv', hR⟩ := hrep
  have hq' : ‖q‖₊ < 1 := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]; exact hq
  obtain ⟨hXu, hXv, hcase⟩ := transport_core_RE hq0 hq' hp hu' hv'
  have hD1 := hreg u' v' hR
  rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rw [h3, h1, h2, hXu, hXv] at hD1
  · linear_combination hD1
  · linear_combination -hD1

lemma exists_latticeRep_norm (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hw0 : w ≠ 0) :
    ∃ w' : K, LatticeRep q w w' ∧ ‖q‖ ≤ ‖w'‖ * ‖w'‖ ∧ ‖w'‖ ≤ 1 ∧
      (‖w'‖ * ‖w'‖ = ‖q‖ → OnHalfLattice q w) := by
  obtain ⟨m, hm1, hm2⟩ := exists_zpow_mul_norm_Ioc hq0 hq hw0
  have ht0 : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hA0 : (0 : ℝ) < ‖q ^ m * w‖ := lt_trans ht0 hm1
  by_cases hcase : ‖q‖ ≤ ‖q ^ m * w‖ * ‖q ^ m * w‖
  · exact ⟨q ^ m * w, ⟨m, Or.inl rfl⟩, hcase, hm2, fun heq => ⟨m, heq⟩⟩
  · push Not at hcase
    have hB : ‖(q : K) ^ (1 - m) * w⁻¹‖ = ‖q‖ / ‖q ^ m * w‖ := by
      rw [norm_mul, norm_inv, norm_zpow, norm_mul, norm_zpow,
        zpow_sub₀ (ne_of_gt ht0), zpow_one, ← div_eq_mul_inv, div_div]
    have hA2 : (0 : ℝ) < ‖q ^ m * w‖ * ‖q ^ m * w‖ := mul_pos hA0 hA0
    refine ⟨q ^ (1 - m) * w⁻¹, ⟨1 - m, Or.inr rfl⟩, ?_, ?_, ?_⟩
    ·
      rw [hB, div_mul_div_comm, le_div_iff₀ hA2]
      exact mul_le_mul_of_nonneg_left hcase.le ht0.le
    ·
      rw [hB, div_le_one hA0]
      exact hm1.le
    ·
      intro heq
      exfalso
      rw [hB, div_mul_div_comm, div_eq_iff (ne_of_gt hA2)] at heq
      have h1 : ‖q‖ * (‖q ^ m * w‖ * ‖q ^ m * w‖) < ‖q‖ * ‖q‖ :=
        mul_lt_mul_of_pos_left hcase ht0
      linarith

lemma exists_expansionRegion_latticeRep (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hp : AddParams q u v)
    (hloc : ¬ (OnHalfLattice q u ∧ OnHalfLattice q v)) :
    ∃ u' v' : K, LatticeRep q u u' ∧ LatticeRep q v v' ∧ ExpansionRegion q u' v' := by
  obtain ⟨u', hu', hu'sq, hu'le, hu'det⟩ := exists_latticeRep_norm hq0 hq hp.u_ne_zero
  obtain ⟨v', hv', hv'sq, hv'le, hv'det⟩ := exists_latticeRep_norm hq0 hq hp.v_ne_zero
  have hP : AddParams q u' v' := hp.latticeRep hu' hv'
  have ht0 : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hu'pos : (0 : ℝ) < ‖u'‖ := norm_pos_iff.mpr hP.u_ne_zero
  have hv'pos : (0 : ℝ) < ‖v'‖ := norm_pos_iff.mpr hP.v_ne_zero

  have hu'lo : ‖q‖ < ‖u'‖ := by
    by_contra hle
    push Not at hle
    have h1 : ‖u'‖ * ‖u'‖ ≤ ‖q‖ * ‖q‖ := mul_le_mul hle hle (norm_nonneg _) ht0.le
    have h2 : ‖q‖ * 1 ≤ ‖q‖ * ‖q‖ := by rw [mul_one]; exact le_trans hu'sq h1
    have h3 : (1 : ℝ) ≤ ‖q‖ := le_of_mul_le_mul_left h2 ht0
    linarith
  have hv'lo : ‖q‖ < ‖v'‖ := by
    by_contra hle
    push Not at hle
    have h1 : ‖v'‖ * ‖v'‖ ≤ ‖q‖ * ‖q‖ := mul_le_mul hle hle (norm_nonneg _) ht0.le
    have h2 : ‖q‖ * 1 ≤ ‖q‖ * ‖q‖ := by rw [mul_one]; exact le_trans hv'sq h1
    have h3 : (1 : ℝ) ≤ ‖q‖ := le_of_mul_le_mul_left h2 ht0
    linarith

  have hprod : ‖q‖ < ‖u'‖ * ‖v'‖ := by
    by_contra hcon
    push Not at hcon
    have e1 : (‖u'‖ * ‖v'‖) * (‖u'‖ * ‖v'‖) ≤ ‖q‖ * ‖q‖ :=
      mul_le_mul hcon hcon (by positivity) ht0.le
    rcases not_and_or.mp hloc with h | h
    · have hu'strict : ‖q‖ < ‖u'‖ * ‖u'‖ :=
        lt_of_le_of_ne hu'sq (fun heq => h (hu'det heq.symm))
      have e2 : ‖q‖ * ‖q‖ ≤ (‖v'‖ * ‖v'‖) * ‖q‖ := mul_le_mul_of_nonneg_right hv'sq ht0.le
      have e3 : (‖v'‖ * ‖v'‖) * ‖q‖ < (‖v'‖ * ‖v'‖) * (‖u'‖ * ‖u'‖) :=
        mul_lt_mul_of_pos_left hu'strict (by positivity)
      nlinarith [e1, e2, e3]
    · have hv'strict : ‖q‖ < ‖v'‖ * ‖v'‖ :=
        lt_of_le_of_ne hv'sq (fun heq => h (hv'det heq.symm))
      have e2 : ‖q‖ * ‖q‖ ≤ (‖u'‖ * ‖u'‖) * ‖q‖ := mul_le_mul_of_nonneg_right hu'sq ht0.le
      have e3 : (‖u'‖ * ‖u'‖) * ‖q‖ < (‖u'‖ * ‖u'‖) * (‖v'‖ * ‖v'‖) :=
        mul_lt_mul_of_pos_left hv'strict (by positivity)
      nlinarith [e1, e2, e3]
  have hqu1 : ‖q‖ * ‖u'‖ ≤ ‖q‖ := by
    have := mul_le_mul_of_nonneg_left hu'le ht0.le
    rwa [mul_one] at this
  have hqv1 : ‖q‖ * ‖v'‖ ≤ ‖q‖ := by
    have := mul_le_mul_of_nonneg_left hv'le ht0.le
    rwa [mul_one] at this
  refine ⟨u', v', hu', hv', ⟨hP, hq, hu'lo, ?_, hv'lo, ?_, ?_, ?_, ?_, ?_⟩⟩
  · linarith
  · linarith
  · rw [norm_mul]; exact hprod
  · rw [norm_mul]
    have h1 : ‖u'‖ * ‖v'‖ ≤ 1 * 1 := mul_le_mul hu'le hv'le (norm_nonneg _) zero_le_one
    rw [mul_one] at h1
    have h2 : ‖q‖ * (‖u'‖ * ‖v'‖) ≤ ‖q‖ * 1 := mul_le_mul_of_nonneg_left h1 ht0.le
    rw [mul_one] at h2
    linarith
  · rw [norm_mul, norm_inv, ← div_eq_mul_inv, lt_div_iff₀ hv'pos]
    linarith
  · rw [norm_mul, norm_inv, ← div_eq_mul_inv, ← mul_div_assoc, div_lt_one hv'pos]
    linarith

theorem symAdd_sum_of_region_of_not_halfLattice (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hreg : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hp : AddParams q u v) (hloc : ¬ (OnHalfLattice q u ∧ OnHalfLattice q v)) :
    (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v) :=
  symAdd_sum_of_region_latticeRep hq0 hq hreg hp
    (exists_expansionRegion_latticeRep hq0 hq hp hloc)

theorem diff_identity_of_region_of_not_halfLattice (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hreg : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v')))
    (hp : AddParams q u v) (hloc : ¬ (OnHalfLattice q u ∧ OnHalfLattice q v)) :
    (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)) :=
  diff_identity_of_region_latticeRep hq0 hq hreg hp
    (exists_expansionRegion_latticeRep hq0 hq hp hloc)

end TateCurve
p2m_reactivate "P2MW.S_TateCurve_ks17_A_exports.TateCurve"

p2m_open "TateCurve~tsum_succ_prod_eq_tsum_divisors" in open _root_.P2MW.S_TateCurve_ks17_A_exports.TateCurve in
open scoped NNReal in
theorem solution :

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K},
      psiCoeffFull u 0 = 2 * yfun u + xfun u) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (N : ℕ),
      psiCoeffFull u (N + 1) = ∑ d ∈ (N + 1).divisors, (d : K) ^ 2 * (u ^ d - u⁻¹ ^ d)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {A Bc : ℕ → K} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ q' : K, q' ≠ 0 → ‖q'‖ < ε → ∃ S : K,
      HasSum (fun N => A N * q' ^ N) S ∧ HasSum (fun N => Bc N * q' ^ N) S),
      ∀ N, A N = Bc N) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} (hq0 : q ≠ 0),
      addDefectDiff q (q * u) v = addDefectDiff q u v) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q' w v : K} (hq'0 : q' ≠ 0)
    (hlo : ‖q'‖ < ‖w‖) (hhi : ‖q'‖ * ‖w‖ < 1) (hwne : ‖w‖ ≠ 1)
    (hv : ‖v‖ = 1) (hv1 : v ≠ 1),
      ExpansionRegion q' w v) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (hrow : ∀ q' u' v' : K, ExpansionRegion q' u' v' → ∀ M : ℕ,
      addDefectSumCoeff u' v' M
        = ∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k + u'⁻¹ ^ k - 2)),
      ∀ q' u' v' : K, ExpansionRegion q' u' v' → HasSum (fun M : ℕ => (∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k + u'⁻¹ ^ k - 2)) * q' ^ M) (addDefectSum q' u' v')) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {f : K → K → ℕ → K}
    (hcoeff : ∀ q' u' v' : K, ExpansionRegion q' u' v' → ∀ M : ℕ,
      f u' v' M = addDefectDiffCoeff u' v' M),
      ∀ q' u' v' : K, ExpansionRegion q' u' v' → HasSum (fun M : ℕ => f u' v' M * q' ^ M) (addDefectDiff q' u' v')) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u * v ≠ 1) (huv' : u * v⁻¹ ≠ 1),
      addDefectDiffCoeff u v 0 = 0) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (q x y : K),
      y - (curve q).toAffine.negY x y = 2 * y + x) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hreg : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hp : AddParams q u v) (hloc : ¬ (OnHalfLattice q u ∧ OnHalfLattice q v)),
      (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = symSumNum q (pointX q u) (pointX q v)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hreg : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v')))
    (hp : AddParams q u v) (hloc : ¬ (OnHalfLattice q u ∧ OnHalfLattice q v)),
      (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q w : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hw : ‖w‖ = 1),
      ¬ OnHalfLattice q w) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} (hreg : ExpansionRegion q u v),
      HasSum (fun N : ℕ => addDefectSumCoeff u v N * q ^ N) (addDefectSum q u v)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u * v ≠ 1) (huv' : u * v⁻¹ ≠ 1),
      addDefectSumCoeff u v 0 = 0) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K},
      addDefectDiff q u v = 0 ↔ (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K},
      addDefectDiff q u v = 0 ↔ (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = -((pointY q u - (curve q).toAffine.negY (pointX q u) (pointY q u)) * (pointY q v - (curve q).toAffine.negY (pointX q v) (pointY q v)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} {u' v' : K} (hp : AddParams q u v)
    (hu' : LatticeRep q u u') (hv' : LatticeRep q v v'),
      AddParams q u' v') :=
  ⟨TateCurve.psiCoeffFull_zero,
   TateCurve.psiCoeffFull_succ_eq_divisorSum,
   TateCurve.coeff_eq_of_hasSum_eq,
   TateCurve.addDefectDiff_q_mul_left,
   TateCurve.expansionRegion_of_spectator,
   TateCurve.rowExpansion_of_coeff_eq,
   TateCurve.diffExpansion_of_coeff_eq,
   TateCurve.addDefectDiffCoeff_zero,
   TateCurve.sub_negY_curve,
   TateCurve.symAdd_sum_of_region_of_not_halfLattice,
   TateCurve.diff_identity_of_region_of_not_halfLattice,
   TateCurve.not_onHalfLattice_of_norm_eq_one,
   TateCurve.addDefectSum_qExpansion,
   TateCurve.addDefectSumCoeff_zero,
   TateCurve.addDefectDiff_eq_zero_iff',
   TateCurve.addDefectDiff_eq_zero_iff_curve,
   TateCurve.AddParams.latticeRep⟩

end S_TateCurve_ks17_A_exports
end P2MW
export P2MW.S_TateCurve_ks17_A_exports (solution)
