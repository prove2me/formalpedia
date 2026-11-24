-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_totient_gamma_lower
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T20:06:34.109417+00:00
-- url     : https://prove2.me/submissions/5b7f3df2-2c10-4572-822a-c64a9d656697

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic
set_option maxRecDepth 1000000

open Real Filter

set_option maxHeartbeats 2000000

namespace TaoFivePrimes


lemma pw (k : ℕ) (hk : 201 ≤ k) :
    2/(2*(k:ℝ)+1) + (2/3)/((2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1)) - 1/((k:ℝ)+1)
      ≤ 18/((6*(k:ℝ)+1)*(6*(k:ℝ)+7)) := by
  have hk403 : (403:ℝ) ≤ 2*(k:ℝ)+1 := by exact_mod_cast (by omega : 403 ≤ 2*k+1)
  have h2 : (0:ℝ) < 2*(k:ℝ)+1 := by linarith
  have hsq : (0:ℝ) < (2*(k:ℝ)+1)^2 - 1 := by nlinarith [sq_nonneg ((2*(k:ℝ)+1) - 403), hk403]
  have hk1 : (0:ℝ) < (k:ℝ)+1 := by positivity
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have h6 : (0:ℝ) < 6*(k:ℝ)+1 := by linarith
  have h7 : (0:ℝ) < 6*(k:ℝ)+7 := by linarith
  have hu : (0:ℝ) ≤ (k:ℝ) - 201 := by linarith
  have hA : 2/(2*(k:ℝ)+1) + (2/3)/((2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1))
      = (6*((2*(k:ℝ)+1)^2 - 1) + 2)/(3*(2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1)) := by
    field_simp <;> ring_nf
  have hB : 18/((6*(k:ℝ)+1)*(6*(k:ℝ)+7)) + 1/((k:ℝ)+1)
      = (18*((k:ℝ)+1) + (6*(k:ℝ)+1)*(6*(k:ℝ)+7))/((6*(k:ℝ)+1)*(6*(k:ℝ)+7)*((k:ℝ)+1)) := by
    field_simp <;> ring_nf
  suffices hs : (6*((2*(k:ℝ)+1)^2 - 1) + 2)/(3*(2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1))
      ≤ (18*((k:ℝ)+1) + (6*(k:ℝ)+1)*(6*(k:ℝ)+7))/((6*(k:ℝ)+1)*(6*(k:ℝ)+7)*((k:ℝ)+1)) by
    linarith [hA, hB]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 3*(2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1))]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by positivity : (0:ℝ) < ((6*(k:ℝ)+1)*(6*(k:ℝ)+7))*((k:ℝ)+1))]
  have hdec : (0:ℝ) ≤ 36*((k:ℝ)-201)^2 + 14494*((k:ℝ)-201) + 1458844 := by positivity
  nlinarith [hdec, hu, sq_nonneg ((k:ℝ)-201)]



lemma log_series_le (k : ℕ) (hk : 1 ≤ k) :
    Real.log (1 + 1/(k:ℝ)) ≤
      2/(2*(k:ℝ)+1) + (2/3)/((2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1)) := by
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have ha : (0:ℝ) ≤ 1/(k:ℝ) := by positivity
  have hHS : HasSum (fun j : ℕ => 2 * (1 / (2 * (j:ℝ) + 1)) * ((1/(k:ℝ)) / ((1/(k:ℝ)) + 2)) ^ (2 * j + 1))
      (Real.log (1 + 1/(k:ℝ))) := Real.hasSum_log_one_add ha
  have hq : (1/(k:ℝ)) / ((1/(k:ℝ)) + 2) = 1/(2*(k:ℝ)+1) := by
    field_simp
    ring
  simp only [hq] at hHS
  have hsumm : Summable (fun j : ℕ => 2 * (1 / (2 * (j:ℝ) + 1)) * (1/(2*(k:ℝ)+1)) ^ (2 * j + 1)) :=
    hHS.summable
  have hsplit := Summable.sum_add_tsum_nat_add 1 hsumm
  rw [Finset.sum_range_one, hHS.tsum_eq] at hsplit
  have htail_le : (∑' i : ℕ, (fun j : ℕ => 2 * (1 / (2 * (j:ℝ) + 1)) * (1/(2*(k:ℝ)+1)) ^ (2 * j + 1)) (i+1))
      ≤ (2/3) * (1/(2*(k:ℝ)+1))^3 / (1 - (1/(2*(k:ℝ)+1))^2) := by
    have hq0 : (0:ℝ) ≤ (1/(2*(k:ℝ)+1))^2 := sq_nonneg _
    have hq1 : (1/(2*(k:ℝ)+1))^2 < 1 := by
      rw [div_pow, one_pow, div_lt_one (by positivity)]
      nlinarith [hk0, sq_nonneg ((k:ℝ))]
    have hgeo : HasSum (fun j : ℕ => (2/3) * (1/(2*(k:ℝ)+1))^3 * ((1/(2*(k:ℝ)+1))^2)^j)
        ((2/3) * (1/(2*(k:ℝ)+1))^3 / (1 - (1/(2*(k:ℝ)+1))^2)) := by
      have := (hasSum_geometric_of_norm_lt_one
        (show ‖(1/(2*(k:ℝ)+1))^2‖ < 1 by rwa [Real.norm_eq_abs, abs_of_nonneg hq0])).mul_left
        ((2/3) * (1/(2*(k:ℝ)+1))^3)
      rwa [div_eq_mul_inv]
    have hmain := ((summable_nat_add_iff 1).mpr hsumm).tsum_le_tsum (fun j => by
      push_cast
      have hcoe : 2 * (1 / (2 * ((j:ℝ) + 1) + 1)) ≤ 2/3 := by
        rw [show 2 * (1 / (2 * ((j:ℝ) + 1) + 1)) = 2/(2*((j:ℝ)+1)+1) by ring]
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*((j:ℝ)+1)+1)]
        linarith
      have hpow : (1/(2*(k:ℝ)+1)) ^ (2 * (j + 1) + 1)
          = (1/(2*(k:ℝ)+1))^3 * ((1/(2*(k:ℝ)+1))^2)^j := by
        rw [show 2 * (j + 1) + 1 = 3 + 2 * j by omega, pow_add, pow_mul]
      calc 2 * (1 / (2 * ((j:ℝ) + 1) + 1)) * (1/(2*(k:ℝ)+1)) ^ (2 * (j + 1) + 1)
          = (2 * (1 / (2 * ((j:ℝ) + 1) + 1))) * ((1/(2*(k:ℝ)+1))^3 * ((1/(2*(k:ℝ)+1))^2)^j) := by
            rw [hpow]
        _ ≤ (2/3) * ((1/(2*(k:ℝ)+1))^3 * ((1/(2*(k:ℝ)+1))^2)^j) := by
            apply mul_le_mul_of_nonneg_right hcoe
            positivity
        _ = (2/3) * (1/(2*(k:ℝ)+1))^3 * ((1/(2*(k:ℝ)+1))^2)^j := by ring) hgeo.summable
    exact hmain.trans_eq hgeo.tsum_eq
  have hconv : (2/3) * (1/(2*(k:ℝ)+1))^3 / (1 - (1/(2*(k:ℝ)+1))^2)
      = (2/3)/((2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1)) := by
    field_simp
  have hlog : Real.log (1 + 1/(k:ℝ)) = 2 * (1/(2*(k:ℝ)+1))
      + (∑' i : ℕ, (fun j : ℕ => 2 * (1 / (2 * (j:ℝ) + 1)) * (1/(2*(k:ℝ)+1)) ^ (2 * j + 1)) (i+1)) := by
    rw [← hsplit]
    congr 1
    norm_num
  have hid : 2 * (1/(2*(k:ℝ)+1)) = 2/(2*(k:ℝ)+1) := by ring
  have htail_le' : (∑' i : ℕ, (fun j : ℕ => 2 * (1 / (2 * (j:ℝ) + 1)) * (1/(2*(k:ℝ)+1)) ^ (2 * j + 1)) (i+1))
      ≤ (2/3)/((2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1)) := htail_le.trans_eq hconv
  rw [hlog]
  linarith [htail_le', hid]


lemma term_le (k : ℕ) (hk : 201 ≤ k) :
    ZetaAsymptotics.term k 1 ≤ 18/((6*(k:ℝ)+1)*(6*(k:ℝ)+7)) := by
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  rw [ZetaAsymptotics.term_one (by omega : 0 < k)]
  have h1 : Real.log ((k:ℝ)+1) - Real.log (k:ℝ) = Real.log (1 + 1/(k:ℝ)) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [h1]
  linarith [log_series_le k (by omega : 1 ≤ k), pw k hk]

lemma tail_bound : (∑' k : ℕ, ZetaAsymptotics.term (k + 201) 1) ≤ 3/1207 := by
  have htel : ∀ k : ℕ, (18:ℝ)/((6*(((k+201:ℕ)):ℝ)+1)*(6*(((k+201:ℕ)):ℝ)+7))
      = (1/2)/((k:ℝ)+201+1/6) - (1/2)/(((k+1:ℕ):ℝ)+201+1/6) := by
    intro k
    push_cast
    have h1 : (6*((k:ℝ)+201)+1) ≠ 0 := by positivity
    have h2 : (6*((k:ℝ)+201)+7) ≠ 0 := by positivity
    have h3 : ((k:ℝ)+201+1/6) ≠ 0 := by positivity
    have h4 : ((k:ℝ)+1+201+1/6) ≠ 0 := by positivity
    field_simp [h1, h2, h3, h4]
    ring
  have hu_tend : Tendsto (fun n : ℕ => (1/2)/((n:ℝ)+201+1/6)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n:ℝ) + (201 + 1/6))) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => (((n:ℝ) + (201 + 1/6)))⁻¹) atTop (nhds 0) := h1.inv_tendsto_atTop
    have h3 : Tendsto (fun n : ℕ => (1/2) * (((n:ℝ) + (201 + 1/6)))⁻¹) atTop (nhds (1/2 * 0)) :=
      tendsto_const_nhds.mul h2
    rw [mul_zero] at h3
    simpa [div_eq_mul_inv, add_assoc] using h3
  have hRsum : HasSum (fun k : ℕ => (18:ℝ)/((6*(((k+201:ℕ)):ℝ)+1)*(6*(((k+201:ℕ)):ℝ)+7)))
      ((1/2)/((201:ℝ)+1/6)) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => by positivity)]
    have hps : ∀ n, ∑ k ∈ Finset.range n, (18:ℝ)/((6*(((k+201:ℕ)):ℝ)+1)*(6*(((k+201:ℕ)):ℝ)+7))
        = (1/2)/((0:ℝ)+201+1/6) - (1/2)/((n:ℝ)+201+1/6) := by
      intro n
      calc ∑ k ∈ Finset.range n, (18:ℝ)/((6*(((k+201:ℕ)):ℝ)+1)*(6*(((k+201:ℕ)):ℝ)+7))
          = ∑ k ∈ Finset.range n, ((1/2)/((k:ℝ)+201+1/6) - (1/2)/(((k+1:ℕ):ℝ)+201+1/6)) := by
            apply Finset.sum_congr rfl
            intro k _
            exact htel k
        _ = -(∑ k ∈ Finset.range n, ((1/2)/(((k+1:ℕ):ℝ)+201+1/6) - (1/2)/((k:ℝ)+201+1/6))) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k _
            ring
        _ = -((1/2)/((n:ℝ)+201+1/6) - (1/2)/(((0:ℕ):ℝ)+201+1/6)) := by
            rw [Finset.sum_range_sub (fun k : ℕ => (1/2)/((k:ℝ)+201+1/6)) n]
        _ = (1/2)/((0:ℝ)+201+1/6) - (1/2)/((n:ℝ)+201+1/6) := by
            simp only [Nat.cast_zero]
            ring
    simp_rw [hps]
    simpa using tendsto_const_nhds.sub hu_tend
  have hsumg : Summable (fun k : ℕ => ZetaAsymptotics.term (k + 201) 1) := by
    have hf : Summable (fun n : ℕ => ZetaAsymptotics.term (n+1) 1) :=
      ZetaAsymptotics.term_tsum_one.summable
    exact (summable_nat_add_iff 200).mpr hf
  have hRsummable : Summable (fun k : ℕ =>
      (18:ℝ)/((6*(((k+201:ℕ)):ℝ)+1)*(6*(((k+201:ℕ)):ℝ)+7))) := hRsum.summable
  have key := hsumg.tsum_le_tsum (fun k => term_le (k+201) (by omega)) hRsummable
  rw [hRsum.tsum_eq] at key
  norm_num at key ⊢
  exact key

/-- Lower bound for Euler--Mascheroni: `57721565/10^8 ≤ γ`. -/
theorem solution : (57721565/10^8 : ℝ) ≤ Real.eulerMascheroniConstant := by
  have hf : Summable (fun n : ℕ => ZetaAsymptotics.term (n+1) 1) :=
    ZetaAsymptotics.term_tsum_one.summable
  have hsplit := Summable.sum_add_tsum_nat_add 200 hf
  rw [ZetaAsymptotics.term_tsum_one.tsum_eq] at hsplit
  have htail_eq : (∑' i : ℕ, (fun n : ℕ => ZetaAsymptotics.term (n+1) 1) (i+200))
      = (∑' k : ℕ, ZetaAsymptotics.term (k+201) 1) := by
    apply tsum_congr
    intro i
    congr 1
  rw [htail_eq] at hsplit
  have htermSum : (∑ i ∈ Finset.range 200, ZetaAsymptotics.term (i+1) 1)
      = Real.log 201 - (harmonic 201 : ℝ) + 1 := by
    have h := ZetaAsymptotics.termSum_one 200
    unfold ZetaAsymptotics.termSum at h
    rw [show ((200:ℕ):ℝ) + 1 = 201 by norm_num, show (200 + 1 : ℕ) = 201 by norm_num] at h
    exact h
  rw [htermSum] at hsplit
  have hγ : Real.eulerMascheroniConstant = (harmonic 201 : ℝ) - Real.log 201
      - (∑' k : ℕ, ZetaAsymptotics.term (k+201) 1) := by
    linarith
  have hr : Real.log 201 ≤ (530330491/10^8 : ℝ) := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 201)]
    calc (201:ℝ) ≤ (2.7182818283:ℝ)^5 * (∑ i ∈ Finset.range 10, (30330491/10^8:ℝ)^i / (i.factorial : ℝ)) := by
          norm_num
      _ ≤ (Real.exp 1)^5 * Real.exp (30330491/10^8) := by
          gcongr
          · exact le_of_lt Real.exp_one_gt_d9
          · exact Real.sum_le_exp_of_nonneg (by norm_num) 10
      _ = Real.exp 5 * Real.exp (30330491/10^8) := by
          rw [← Real.exp_nat_mul 1 5]
          norm_num
      _ = Real.exp (5 + 30330491/10^8) := by rw [← Real.exp_add]
      _ = Real.exp (530330491/10^8) := by norm_num
  have hnum : (57721565/10^8 : ℝ) ≤ (harmonic 201 : ℝ) - (530330491/10^8) - 3/1207 := by
    norm_num [harmonic]
  calc (57721565/10^8 : ℝ) ≤ (harmonic 201 : ℝ) - (530330491/10^8) - 3/1207 := hnum
    _ ≤ Real.eulerMascheroniConstant := by
        rw [hγ]
        linarith [hr, tail_bound]

end TaoFivePrimes

open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : (57721565/10^8 : ℝ) ≤ Real.eulerMascheroniConstant :=
  TaoFivePrimes.solution

#print axioms solution
