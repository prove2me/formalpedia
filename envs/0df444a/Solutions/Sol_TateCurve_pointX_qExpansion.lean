-- Prove2me | solution 1 for TateCurve.pointX_qExpansion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/6f6d2266-86c6-545b-9517-9ce670032139

import Definitions.Def_TateCurve_PointSeries
import Definitions.Def_TateCurve_Tails
import Theorems.Thm_TateCurve_pointX_normalForm
import Theorems.Thm_TateCurve_hasSum_xfun
import Theorems.Thm_TateCurve_hasSum_yfun
import Theorems.Thm_TateCurve_tsum_succ_prod_eq_tsum_divisors
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_pointX_qExpansion

set_option autoImplicit false
open scoped NNReal
open IsUltrametricDist Filter

namespace TateCurve
p2m_export "TateCurve" "xfun yfun pointX term b xDivTerm yDivTerm xCoeff growthBound one_le_growthBound norm_xDivTerm_le pointX_normalForm hasSum_xfun hasSum_yfun tsum_succ_prod_eq_tsum_divisors"
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

private theorem tsum_succ_prod_eq_tsum_divisors_loc (hC1 : 1 ≤ C)
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

section QExpansion

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q u : K}

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

private theorem nnnorm_pow_mul_lt_one (hq : ‖q‖₊ < 1) (hqv : ‖q * u‖₊ < 1) (n : ℕ) :
    ‖q ^ (n + 1) * u‖₊ < 1 := by
  have hrw : q ^ (n + 1) * u = q ^ n * (q * u) := by ring
  rw [hrw, nnnorm_mul, nnnorm_pow]
  calc ‖q‖₊ ^ n * ‖q * u‖₊ ≤ 1 * ‖q * u‖₊ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ zero_le hq.le) zero_le
    _ = ‖q * u‖₊ := one_mul _
    _ < 1 := hqv

private theorem nnnorm_pow_lt_one (hq : ‖q‖₊ < 1) (n : ℕ) : ‖q ^ (n + 1)‖₊ < 1 := by
  rw [nnnorm_pow]
  exact pow_lt_one₀ zero_le hq (Nat.succ_ne_zero n)

private theorem hasSum_yfun_succ {w : K} (hw : ‖w‖₊ < 1) :
    HasSum (fun m : ℕ => (((m + 1).choose 2 : ℕ) : K) * w ^ (m + 1)) (yfun w) := by

  have hsummable : Summable fun m : ℕ => (((m + 1).choose 2 : ℕ) : K) * w ^ (m + 1) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [Nat.cofinite_eq_atTop]
    have hw' : ‖w‖ < 1 := hw
    have hlim : Filter.Tendsto (fun m : ℕ => ‖w‖ ^ (m + 1)) Filter.atTop (nhds 0) := by
      have h0 : Filter.Tendsto (fun m : ℕ => ‖w‖ ^ m) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg w) hw'
      simpa [Function.comp_def] using h0.comp (Filter.tendsto_add_atTop_nat 1)
    refine squeeze_zero_norm (fun m => ?_) hlim
    calc ‖(((m + 1).choose 2 : ℕ) : K) * w ^ (m + 1)‖
        = ‖(((m + 1).choose 2 : ℕ) : K)‖ * ‖w ^ (m + 1)‖ := norm_mul _ _
      _ ≤ 1 * ‖w ^ (m + 1)‖ :=
          mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_natCast_le_one K _)
            (norm_nonneg _)
      _ = ‖w‖ ^ (m + 1) := by rw [one_mul, norm_pow]

  have htsum : ∑' m : ℕ, (((m + 1).choose 2 : ℕ) : K) * w ^ (m + 1) = yfun w := by
    rw [hsummable.tsum_eq_zero_add]
    have h0 : (((0 + 1).choose 2 : ℕ) : K) * w ^ (0 + 1) = 0 := by
      norm_num [show Nat.choose 1 2 = 0 from rfl]
    have hshift : (fun m : ℕ => (((m + 1 + 1).choose 2 : ℕ) : K) * w ^ (m + 1 + 1))
        = fun m : ℕ => (((m + 2).choose 2 : ℕ) : K) * w ^ (m + 2) := by
      funext m
      norm_num
    rw [h0, zero_add, hshift]
    exact (TateCurve.hasSum_yfun hw).tsum_eq
  exact htsum ▸ hsummable.hasSum

private theorem hasSum_xRow (hq : ‖q‖₊ < 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1)
    (n : ℕ) :
    HasSum (fun m : ℕ => xDivTerm u (m + 1) * q ^ ((n + 1) * (m + 1)))
      (xfun (q ^ (n + 1) * u) + xfun (q ^ (n + 1) * u⁻¹) - 2 * xfun (q ^ (n + 1))) := by
  have h1 := TateCurve.hasSum_xfun (nnnorm_pow_mul_lt_one hq hqu n)
  have h2 := TateCurve.hasSum_xfun (nnnorm_pow_mul_lt_one hq hqu' n)
  have h3 := (TateCurve.hasSum_xfun (nnnorm_pow_lt_one hq n)).mul_left (2 : K)
  have hcomb := (h1.add h2).sub h3
  have hfun : (fun m : ℕ =>
      ((m + 1 : ℕ) : K) * (q ^ (n + 1) * u) ^ (m + 1)
        + ((m + 1 : ℕ) : K) * (q ^ (n + 1) * u⁻¹) ^ (m + 1)
        - 2 * (((m + 1 : ℕ) : K) * (q ^ (n + 1)) ^ (m + 1)))
      = fun m : ℕ => xDivTerm u (m + 1) * q ^ ((n + 1) * (m + 1)) := by
    funext m
    rw [xDivTerm, mul_pow, mul_pow, ← pow_mul]
    ring
  rw [hfun] at hcomb
  exact hcomb

private theorem hasSum_yRow (hq : ‖q‖₊ < 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1)
    (n : ℕ) :
    HasSum (fun m : ℕ => yDivTerm u (m + 1) * q ^ ((n + 1) * (m + 1)))
      (yfun (q ^ (n + 1) * u) - yfun (q ^ (n + 1) * u⁻¹) - xfun (q ^ (n + 1) * u⁻¹)
        + xfun (q ^ (n + 1))) := by
  have h1 := hasSum_yfun_succ (nnnorm_pow_mul_lt_one hq hqu n)
  have h2 := hasSum_yfun_succ (nnnorm_pow_mul_lt_one hq hqu' n)
  have h3 := TateCurve.hasSum_xfun (nnnorm_pow_mul_lt_one hq hqu' n)
  have h4 := TateCurve.hasSum_xfun (nnnorm_pow_lt_one hq n)
  have hcomb := ((h1.sub h2).sub h3).add h4
  have hfun : (fun m : ℕ =>
      (((m + 1).choose 2 : ℕ) : K) * (q ^ (n + 1) * u) ^ (m + 1)
        - (((m + 1).choose 2 : ℕ) : K) * (q ^ (n + 1) * u⁻¹) ^ (m + 1)
        - ((m + 1 : ℕ) : K) * (q ^ (n + 1) * u⁻¹) ^ (m + 1)
        + ((m + 1 : ℕ) : K) * (q ^ (n + 1)) ^ (m + 1))
      = fun m : ℕ => yDivTerm u (m + 1) * q ^ ((n + 1) * (m + 1)) := by
    funext m
    rw [yDivTerm, mul_pow, mul_pow, ← pow_mul]
    ring
  rw [hfun] at hcomb
  exact hcomb

end QExpansion

end TateCurve

p2m_open "TateCurve P2MW.S_TateCurve_pointX_qExpansion.TateCurve"

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) :
    pointX q u = xfun u + ∑' N : ℕ, xCoeff u (N + 1) * q ^ (N + 1) := by
  have hC1 := one_le_growthBound u
  have hh : ∀ m : ℕ, 0 < m → ‖xDivTerm u m‖ ≤ growthBound u ^ m :=
    fun m _ => norm_xDivTerm_le u m
  have hrC := norm_mul_growthBound_lt_one hq hqu hqu'
  have hdouble : Summable fun p : ℕ × ℕ =>
      xDivTerm u (p.2 + 1) * q ^ ((p.1 + 1) * (p.2 + 1)) :=
    summable_succ_prod_loc hC1 hh hrC
  have hrows : ∑' p : ℕ × ℕ, xDivTerm u (p.2 + 1) * q ^ ((p.1 + 1) * (p.2 + 1))
      = ∑' n : ℕ, (xfun (q ^ (n + 1) * u) + xfun (q ^ (n + 1) * u⁻¹)
          - 2 * xfun (q ^ (n + 1))) := by
    rw [hdouble.tsum_prod]
    exact tsum_congr fun n => (hasSum_xRow hq hqu hqu' n).tsum_eq
  have hdivisors : ∑' p : ℕ × ℕ, xDivTerm u (p.2 + 1) * q ^ ((p.1 + 1) * (p.2 + 1))
      = ∑' N : ℕ, xCoeff u (N + 1) * q ^ (N + 1) := by
    simpa only [xCoeff] using TateCurve.tsum_succ_prod_eq_tsum_divisors hC1 hh hrC
  rw [TateCurve.pointX_normalForm hq0 hq hu0 hu, ← hrows, hdivisors]

end S_TateCurve_pointX_qExpansion
end P2MW
export P2MW.S_TateCurve_pointX_qExpansion (solution)
