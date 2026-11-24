-- Prove2me | solution 1 for TaoFivePrimes.mertens_reciprocal_endpoint_certificate_511
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-29T13:15:39.302219+00:00
-- url     : https://prove2.me/submissions/ce93fb38-9865-414e-b7c5-8d0f41b41d1d

import Mathlib
import Definitions.Def_TaoFivePrimes_mertens_cert_511_tables
import Theorems.Thm_TaoFivePrimes_llb_le_loglog
import Theorems.Thm_TaoFivePrimes_log_le_lub
import Theorems.Thm_TaoFivePrimes_clbZ_table_bounds
import Theorems.Thm_TaoFivePrimes_WLO512_le_sum512
import Theorems.Thm_TaoFivePrimes_step_T_certificate
import Theorems.Thm_TaoFivePrimes_endpoint_certificate
import Theorems.Thm_TaoFivePrimes_mertens_tail_upper_bound

open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false

namespace TaoFivePrimes

private lemma primesLE_succ (k : Nat) :
    Nat.primesLE (k+1) = if (k+1).Prime then insert (k+1) (Nat.primesLE k) else Nat.primesLE k := by
  ext p
  rw [Nat.mem_primesLE]
  by_cases h : (k+1).Prime
  · rw [if_pos h, Finset.mem_insert, Nat.mem_primesLE]
    constructor
    · intro hp
      rcases eq_or_lt_of_le hp.1 with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨by omega, hp.2⟩
    · rintro (rfl | ⟨hle, hpr⟩)
      · exact ⟨le_refl _, h⟩
      · exact ⟨by omega, hpr⟩
  · rw [if_neg h, Nat.mem_primesLE]
    constructor
    · intro hp
      have hne : p ≠ k+1 := fun he => h (he ▸ hp.2)
      exact ⟨by omega, hp.2⟩
    · intro hp; exact ⟨by omega, hp.2⟩


private lemma sum_primesLE_succ {α : Type*} [AddCommMonoid α] (k : Nat) (f : Nat → α) :
    ∑ p ∈ Nat.primesLE (k+1), f p = ∑ p ∈ Nat.primesLE k, f p + if (k+1).Prime then f (k+1) else 0 := by
  rw [primesLE_succ k]
  by_cases h : (k+1).Prime
  · rw [if_pos h, if_pos h, Finset.sum_insert]
    · rw [add_comm]
    · simp only [Nat.mem_primesLE]; omega
  · rw [if_neg h, if_neg h, add_zero]


private lemma loglog_mono {a b : Real} (ha : 1 < a) (h : a ≤ b) :
    Real.log (Real.log a) ≤ Real.log (Real.log b) :=
  Real.log_le_log (Real.log_pos ha) (Real.log_le_log (by linarith) h)


private lemma log_ge_one_sub_inv {x : Real} (hx : 0 < x) : 1 - 1/x ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (show (0:Real) < x⁻¹ by positivity)
  rw [Real.log_inv] at h
  rw [one_div]
  linarith


private lemma neg_log_sub_le (x : Real) (hx0 : 0 < x) (hx : x ≤ 1/4) :
    -Real.log (1 - x) - x ≤ x^2/(2*(1-x)) := by
  have hx1 : |x| < 1 := by rw [abs_of_pos hx0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le (x := x) hx1 3
  obtain ⟨hlow, -⟩ := abs_le.mp h
  have herr : |x|^4/(1 - |x|) ≤ x^4/(1-x) := by rw [abs_of_pos hx0]
  have hsum : (∑ i ∈ Finset.range 3, x^(i+1)/(i+1)) = x + x^2/2 + x^3/3 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  have h2 : -Real.log (1-x) - x ≤ x^2/2 + x^3/3 + x^4/(1-x) := by
    rw [hsum] at hlow
    have := le_trans (neg_le_neg herr) hlow
    linarith
  have h3 : x^2/2 + x^3/3 + x^4/(1-x) ≤ x^2/(2*(1-x)) := by
    rw [le_div_iff₀ (by linarith : (0:Real) < 2*(1-x))]
    have hd0 : (1:Real) - x ≠ 0 := by linarith
    have h1 : x^4/(1-x) * (2*(1-x)) = 2*x^4 := by
      field_simp
    have h2 : x^2/2 * (2*(1-x)) = x^2*(1-x) := by
      field_simp
    have h3 : x^3/3 * (2*(1-x)) = (2/3)*x^3*(1-x) := by
      field_simp
    rw [add_mul, add_mul, h1, h2, h3]
    have h4x : (4:Real)*x - 1 ≤ 0 := by linarith
    nlinarith [hx0, hx, mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hx0.le 3) h4x]
  linarith


private lemma w_ge_small (p : Nat) (hp : 4 ≤ p) :
    -(1/(2*(p:Real)*((p:Real)-1))) ≤ Real.log (1 - 1/(p:Real)) + 1/(p:Real) := by
  have hp0 : (0:Real) < (p:Real) := by positivity
  have hp4 : (4:Real) ≤ (p:Real) := by exact_mod_cast hp
  have hx0 : 0 < 1/(p:Real) := by positivity
  have hx : 1/(p:Real) ≤ 1/4 := by
    rw [div_le_iff₀ hp0]
    linarith
  have h := neg_log_sub_le (1/(p:Real)) hx0 hx
  have hpne : (p:Real) ≠ 0 := ne_of_gt hp0
  have hp1ne : (p:Real) - 1 ≠ 0 := by
    have : (1:Real) < (p:Real) := by linarith
    linarith
  have hx1ne : (1:Real) - 1/(p:Real) ≠ 0 := by
    have : 1/(p:Real) < 1 := by
      rw [div_lt_one hp0]
      linarith
    linarith
  have hxeq : (1/(p:Real))^2/(2*(1-1/(p:Real))) = 1/(2*(p:Real)*((p:Real)-1)) := by
    field_simp
  rw [hxeq] at h
  linarith


private lemma lastP_mem (n : Nat) (hn : 2 ≤ n) (hN : n ≤ 511) : lastP n ∈ pl521 := by
  interval_cases n <;> decide


private lemma firstP_mem (n : Nat) (hn : 2 ≤ n) (hN : n ≤ 511) : firstP n ∈ pl521 := by
  interval_cases n <;> decide


private lemma lastP_le (n : Nat) (hn : 2 ≤ n) (hN : n ≤ 511) : lastP n ≤ n := by
  interval_cases n <;> decide


private lemma lastP_gt_one (n : Nat) (hn : 2 ≤ n) (hN : n ≤ 511) : 1 < lastP n := by
  interval_cases n <;> decide


private lemma firstP_ge (n : Nat) (hn : 2 ≤ n) (hN : n ≤ 511) : n + 1 ≤ firstP n := by
  interval_cases n <;> decide


private lemma lastP_gap (n : Nat) (hn : 2 ≤ n) (hN : n ≤ 511) : n - lastP n < lastP n := by
  interval_cases n <;> decide


private lemma lum_le_log (p : Nat) (hp : p ∈ pl521) :
    ((clbZ p : Nat) : Real)/10000 ≤ Real.log (p : Real) :=
  (clbZ_table_bounds p hp).2

private lemma clbZ_pos (p : Nat) (hp : p ∈ pl521) : 0 < clbZ p :=
  (clbZ_table_bounds p hp).1

private lemma WLOi_512 : WLOi 512 = -315600119 := by decide

private lemma WLO_512_val : WLO 512 = (-315600119/1000000000) := by
  rw [WLO, WLOi_512]
  norm_num


private lemma gamma_ge_glo : glo ≤ Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 1024
  rw [Real.eulerMascheroniSeq] at h
  norm_num at h
  have hH : (300367/40000 : Real) ≤ (harmonic 1024 : Real) := by norm_num [harmonic]
  have hlog : Real.log 1025 ≤ 10 * (6931471808/10000000000 : Real) + 1/1024 := by
    have hsplit : Real.log 1025 = 10 * Real.log 2 + Real.log (1 + 1/1024) := by
      rw [show (1025:Real) = 2^10 * (1 + 1/1024) by norm_num,
          Real.log_mul (by positivity) (by positivity), Real.log_pow]
      ring
    have h2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have h3 : Real.log (1 + 1/1024) ≤ 1/1024 := by
      have := Real.log_le_sub_one_of_pos (show (0:Real) < 1 + 1/1024 by norm_num)
      linarith
    linarith
  have hglo : glo = 300367/40000 - 10 * (6931471808/10000000000 : Real) - 1/1024 := by
    unfold glo
    norm_num
  linarith


private lemma rho1_chain (m d : Nat) (hm : 2 ≤ m) (hd : d < m)
    (hclb : ((clbZ m : Nat) : Real)/10000 ≤ Real.log (m : Real))
    (hclbpos : 0 < clbZ m)
    (hL : Real.log (m : Real) ≤ (lub m : Real)) :
    (rho1f m d : Real) ≤ Real.log (1 + Real.log (1 + (d : Real)/(m : Real))/Real.log (m : Real)) := by
  unfold rho1f
  push_cast
  set x : Real := (d : Real)/(m : Real) with hxdef
  set lum : Real := ((clbZ m : Nat) : Real)/10000 with hlumdef
  have hm_pos : (0:Real) < (m:Real) := by exact_mod_cast (by omega : 0 < m)
  have hb_pos : 0 < Real.log (m:Real) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hlum_pos : 0 < lum := by
    rw [hlumdef]
    exact div_pos (by exact_mod_cast hclbpos) (by norm_num)
  have hx0 : 0 ≤ x := by
    rw [hxdef]
    positivity
  have hx1 : x < 1 := by
    rw [hxdef, div_lt_one hm_pos]
    exact_mod_cast hd
  have hx2 : 0 ≤ x - x^2/2 := by
    have h3 : x^2/2 ≤ x := by
      nlinarith [mul_nonneg hx0 (by linarith : (0:Real) ≤ 2 - x)]
    linarith
  have hL1_lo : x - x^2/2 ≤ Real.log (1 + x) := by
    have h2 : x - x^2/2 ≤ 2*x/(x+2) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith [mul_nonneg hx0 hx0]
    have h := Real.le_log_one_add_of_nonneg hx0
    linarith
  have hL1_hi : Real.log (1 + x) ≤ x := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0:Real) < 1 + x)
    linarith
  have hL1_nn : 0 ≤ Real.log (1 + x) := le_trans hx2 hL1_lo
  set u : Real := Real.log (1 + x)/Real.log (m:Real) with hudef
  have hF : (x - x^2/2)/Real.log (m:Real) - x^2/(2*(Real.log (m:Real))^2) ≤
      Real.log (1 + u) := by
    have hu : 0 ≤ u := by
      rw [hudef]
      exact div_nonneg hL1_nn hb_pos.le
    have h1 : u - u^2/2 ≤ 2*u/(u+2) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith [mul_nonneg hu hu]
    have h4 : 2*u/(u+2) ≤ Real.log (1 + u) := Real.le_log_one_add_of_nonneg hu
    have h5 : (x - x^2/2)/Real.log (m:Real) ≤ u := by
      rw [hudef]
      exact div_le_div_of_nonneg_right hL1_lo hb_pos.le
    have h6 : u^2 ≤ x^2/(Real.log (m:Real))^2 := by
      rw [hudef, div_pow]
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hL1_nn hL1_hi 2) (sq_nonneg _)
    have h7 : u^2/2 ≤ x^2/(2*(Real.log (m:Real))^2) := by
      rw [show x^2/(2*(Real.log (m:Real))^2) = (x^2/(Real.log (m:Real))^2)/2 by ring]
      linarith
    linarith
  have hA1 : (x - x^2/2)/(lub m : Real) - x^2/(2*lum^2) ≤
      (x - x^2/2)/Real.log (m:Real) - x^2/(2*(Real.log (m:Real))^2) := by
    have ha := div_le_div_of_nonneg_left hx2 hb_pos hL
    have hb : x^2/(2*(Real.log (m:Real))^2) ≤ x^2/(2*lum^2) := by
      apply div_le_div_of_nonneg_left (sq_nonneg x)
      · exact mul_pos (by norm_num) (sq_pos_of_pos hlum_pos)
      · nlinarith [hclb, hlum_pos, hb_pos,
          mul_nonneg (sub_nonneg.mpr hclb) (by linarith : (0:Real) ≤ Real.log (m:Real) + lum)]
    linarith
  linarith

private lemma rho2_chain (q g : Nat) (hg : 2 ≤ g) (hgq : g ≤ q)
    (hL : Real.log (q:Real) ≤ (lub q : Real)) :
    (rho2f q (q - g) : Real) ≤ 4/(Real.log (g:Real))^3 - 4/(lub q : Real)^3 := by
  unfold rho2f
  push_cast
  set A : Real := Real.log (g:Real) with hAdef
  set B : Real := (lub q : Real) with hBdef
  have hg0 : (0:Real) < (g:Real) := by exact_mod_cast (by omega : 0 < g)
  have hq0' : (0:Real) < (q:Real) := by exact_mod_cast (by omega : 0 < q)
  have hq0 : (q:Real) ≠ 0 := ne_of_gt hq0'
  have hA : 0 < A := by
    rw [hAdef]
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < g))
  have hAq : A ≤ Real.log (q:Real) := by
    rw [hAdef]
    exact Real.log_le_log hg0 (by exact_mod_cast hgq)
  have hB : 0 < B := by
    rw [hBdef]
    exact lt_of_lt_of_le hA (le_trans hAq hL)
  have hBA : A ≤ B := by
    rw [hBdef]
    exact le_trans hAq hL
  have hD : 0 ≤ ((q - g : Nat) : Real)/(q:Real) := by positivity
  have hDBA : ((q - g : Nat) : Real)/(q:Real) ≤ B - A := by
    have h1 : Real.log ((q:Real)/(g:Real)) = Real.log (q:Real) - A := by
      rw [hAdef]
      exact Real.log_div (ne_of_gt hq0') (ne_of_gt hg0)
    have h2 : 1 - (g:Real)/(q:Real) ≤ Real.log ((q:Real)/(g:Real)) := by
      have h := log_ge_one_sub_inv (x := (q:Real)/(g:Real)) (by positivity)
      rw [one_div_div] at h
      exact h
    have h3 : 1 - (g:Real)/(q:Real) = ((q - g : Nat) : Real)/(q:Real) := by
      rw [Nat.cast_sub hgq]
      field_simp
    have h4 : Real.log (q:Real) ≤ B := by rw [hBdef]; exact hL
    linarith
  have h4A : 4/A^3 - 4/B^3 = 4*(B-A)*(B^2+A*B+A^2)/(A^3*B^3) := by
    have hA0 : A ≠ 0 := ne_of_gt hA
    have hB0 : B ≠ 0 := ne_of_gt hB
    field_simp
    ring
  have step1 : 12*(B-A)/(A*B^3) ≤ 4/A^3 - 4/B^3 := by
    rw [h4A, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (0:Real) ≤ B - A := by linarith
    have hp1 : (0:Real) ≤ (B - A) * (A * B^3) := mul_nonneg h1 (by positivity)
    have hp2 : (0:Real) ≤ (B - A) * (B + 2*A) := mul_nonneg h1 (by linarith)
    nlinarith [mul_nonneg hp1 hp2]
  have step2 : 12*(B-A)/(B^4) ≤ 12*(B-A)/(A*B^3) := by
    apply div_le_div_of_nonneg_left (by linarith : (0:Real) ≤ 12*(B-A)) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hBA (by positivity : (0:Real) ≤ B^3)]
  have step3 : 12*(((q - g : Nat) : Real)/(q:Real))/(B^4) ≤ 12*(B-A)/(B^4) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h := mul_le_mul_of_nonneg_right hDBA (by positivity : (0:Real) ≤ B^4)
    linarith
  have heq : (12 * ((q - g : Nat) : Real) / ((q:Real) * B^4)) =
      12*(((q - g : Nat) : Real)/(q:Real))/(B^4) := by ring
  linarith

private lemma rho1_le (n : Nat) (hn : 2 ≤ n) (hN : n ≤ 511) :
    (rho1 n : Real) ≤ Real.log (Real.log (n:Real)) - (llb (lastP n) : Real) := by
  have hm_mem := lastP_mem n hn hN
  have hllb := llb_le_loglog (lastP n) hm_mem
  have hmono : Real.log (Real.log (lastP n : Real)) ≤ Real.log (Real.log (n:Real)) :=
    loglog_mono (by exact_mod_cast lastP_gt_one n hn hN) (by exact_mod_cast lastP_le n hn hN)
  have hmain : (rho1 n : Real) ≤
      Real.log (Real.log (n:Real)) - Real.log (Real.log (lastP n : Real)) := by
    rw [rho1]
    set m : Nat := lastP n with hmdef
    set d : Nat := n - m with hddef
    have hmle : m ≤ n := by rw [hmdef]; exact lastP_le n hn hN
    have hm : 2 ≤ m := by rw [hmdef]; have h1 := lastP_gt_one n hn hN; omega
    have hd : d < m := by rw [hddef, hmdef]; exact lastP_gap n hn hN
    have hclb : ((clbZ m : Nat) : Real)/10000 ≤ Real.log (m : Real) :=
      lum_le_log m (by rw [hmdef]; exact hm_mem)
    have hclbpos : 0 < clbZ m := clbZ_pos m (by rw [hmdef]; exact hm_mem)
    have hL : Real.log (m : Real) ≤ (lub m : Real) := log_le_lub m (by rw [hmdef]; exact hm_mem)
    have hchain := rho1_chain m d hm hd hclb hclbpos hL
    have hm0 : (m:Real) ≠ 0 := by
      have : (0:Real) < (m:Real) := by exact_mod_cast (by omega : 0 < m)
      linarith
    have hnd : n = m + d := by omega
    have hfac : (n:Real) = (m:Real)*(1 + (d:Real)/(m:Real)) := by
      rw [hnd, mul_add, mul_one, mul_div_cancel₀ _ hm0]
      push_cast
      ring
    have hlogm_pos : 0 < Real.log (m:Real) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
    have hlogx_nn : 0 ≤ Real.log (1 + (d:Real)/(m:Real)) := by
      apply Real.log_nonneg
      have hD : (0:Real) ≤ (d:Real)/(m:Real) := by positivity
      linarith
    have hxd : 0 < Real.log (m:Real) + Real.log (1 + (d:Real)/(m:Real)) := by linarith
    have hx1p0 : (0:Real) < 1 + (d:Real)/(m:Real) := by
      have hD : (0:Real) ≤ (d:Real)/(m:Real) := by positivity
      linarith
    have hlogdiff : Real.log (Real.log (n:Real)) - Real.log (Real.log (m:Real)) =
        Real.log (1 + Real.log (1 + (d:Real)/(m:Real))/Real.log (m:Real)) := by
      have h2 : Real.log (n:Real) = Real.log (m:Real) + Real.log (1 + (d:Real)/(m:Real)) := by
        rw [hfac, Real.log_mul hm0 (ne_of_gt hx1p0)]
      rw [h2, ← Real.log_div (x := Real.log (m:Real) + Real.log (1 + (d:Real)/(m:Real)))
            (y := Real.log (m:Real)) (ne_of_gt hxd) (ne_of_gt hlogm_pos)]
      congr 1
      rw [add_div, div_self (ne_of_gt hlogm_pos)]
    linarith [hchain, hlogdiff]
  linarith

private lemma rho2_le (n : Nat) (hn : 2 ≤ n) (hN : n ≤ 511) :
    (rho2 n : Real) ≤ 4/(Real.log ((n:Real)+1))^3 - 4/(lub (firstP n) : Real)^3 := by
  rw [rho2]
  have hq_mem := firstP_mem n hn hN
  have hq_ge := firstP_ge n hn hN
  have hL : Real.log (firstP n : Real) ≤ (lub (firstP n) : Real) := log_le_lub (firstP n) hq_mem
  have hchain := rho2_chain (firstP n) (n+1) (by omega) hq_ge hL
  have hsub : firstP n - (n+1) = firstP n - n - 1 := by omega
  rw [hsub] at hchain
  have harg : Real.log ((n:Real)+1) = Real.log ((n+1 : Nat) : Real) := by
    rw [Nat.cast_add, Nat.cast_one]
  rw [harg]
  exact hchain

private lemma rho_le (n : Nat) (hn : 2 ≤ n) (hN : n ≤ 511) :
    (rho n : Real) ≤ (Real.log (Real.log (n:Real)) - (llb (lastP n) : Real)) +
      (4/(Real.log ((n:Real)+1))^3 - 4/(lub (firstP n) : Real)^3) := by
  have h1 := rho1_le n hn hN
  have h2 := rho2_le n hn hN
  unfold rho
  push_cast
  linarith


private lemma hmid :
    -(1/2)*(1/512 - 1/8192) ≤
      ∑ p ∈ Nat.primesLE 8192 \ Nat.primesLE 512, (Real.log (1 - 1/(p:Real)) + 1/(p:Real)) := by
  have hpt : ∀ p ∈ Nat.primesLE 8192 \ Nat.primesLE 512,
      -(1/(2*(p:Real)*((p:Real)-1))) ≤ Real.log (1 - 1/(p:Real)) + 1/(p:Real) := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    have hle1 : ¬ p ≤ 512 := fun h => hp.2 (by rw [Nat.mem_primesLE]; exact ⟨h, (Nat.mem_primesLE.mp hp.1).2⟩)
    have := (Nat.mem_primesLE.mp hp.1).1
    exact w_ge_small p (by omega)
  have hneg : ∑ p ∈ Nat.primesLE 8192 \ Nat.primesLE 512, -(Real.log (1 - 1/(p:Real)) + 1/(p:Real)) ≤
      (1/2) * ∑ n ∈ Finset.Ico (513:Nat) 8193, 1/((n:Real)*((n:Real)-1)) := by
    calc ∑ p ∈ Nat.primesLE 8192 \ Nat.primesLE 512, -(Real.log (1 - 1/(p:Real)) + 1/(p:Real))
        ≤ ∑ p ∈ Nat.primesLE 8192 \ Nat.primesLE 512, 1/(2*(p:Real)*((p:Real)-1)) :=
          Finset.sum_le_sum (fun p hp => by linarith [hpt p hp])
      _ ≤ ∑ n ∈ Finset.Ico (513:Nat) 8193, 1/(2*(n:Real)*((n:Real)-1)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            rw [Finset.mem_sdiff, Nat.mem_primesLE] at hp
            have hp512 : ¬ p ≤ 512 := fun h => hp.2 (by rw [Nat.mem_primesLE]; exact ⟨h, hp.1.2⟩)
            have hp8192 : p ≤ 8192 := hp.1.1
            rw [Finset.mem_Ico]
            omega
          · intro n hn hnnot
            have hn513 : 513 ≤ n := (Finset.mem_Ico.mp hn).1
            have hn0 : (0:Real) < (n:Real) := by exact_mod_cast (by omega : 0 < n)
            have hn1 : (0:Real) < (n:Real) - 1 := by
              have : (1:Real) < (n:Real) := by exact_mod_cast (by omega : 1 < n)
              linarith
            positivity
      _ = (1/2) * ∑ n ∈ Finset.Ico (513:Nat) 8193, 1/((n:Real)*((n:Real)-1)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          have hn513 : 513 ≤ n := (Finset.mem_Ico.mp hn).1
          have hn0 : (n:Real) ≠ 0 := by
            have : (0:Real) < (n:Real) := by exact_mod_cast (by omega : 0 < n)
            linarith
          have hn1 : (n:Real) - 1 ≠ 0 := by
            have : (1:Real) < (n:Real) := by exact_mod_cast (by omega : 1 < n)
            linarith
          field_simp
  have hterm : ∀ n ∈ Finset.Ico (513:Nat) 8193,
      1/((n:Real)*((n:Real)-1)) = 1/((n:Real)-1) - 1/(n:Real) := by
    intro n hn
    have hn513 : 513 ≤ n := (Finset.mem_Ico.mp hn).1
    have h2 : (2:Real) ≤ (n:Real) := by exact_mod_cast (by omega : 2 ≤ n)
    have hn0 : (n:Real) ≠ 0 := ne_of_gt (by linarith)
    have hn1 : (n:Real) - 1 ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring
  have htel2 : ∀ k, ∑ n ∈ Finset.Ico (513:Nat) (513 + k), (1/((n:Real)-1) - 1/(n:Real)) =
      1/512 - 1/((512 + k : Nat) : Real) := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
        rw [show 513 + (j+1) = (513 + j) + 1 by omega,
            Finset.sum_Ico_succ_top (by omega : 513 ≤ 513 + j) (fun n => 1/((n:Real)-1) - 1/(n:Real)),
            ih]
        push_cast
        ring
  have htel : ∑ n ∈ Finset.Ico (513:Nat) 8193, 1/((n:Real)*((n:Real)-1)) = 1/512 - 1/8192 := by
    calc ∑ n ∈ Finset.Ico (513:Nat) 8193, 1/((n:Real)*((n:Real)-1))
        = ∑ n ∈ Finset.Ico (513:Nat) 8193, (1/((n:Real)-1) - 1/(n:Real)) :=
          Finset.sum_congr rfl (fun n hn => hterm n hn)
      _ = 1/512 - 1/8192 := by
          rw [show (8193:Nat) = 513 + 7680 by norm_num, htel2 7680]
          norm_num
  rw [Finset.sum_neg_distrib, htel] at hneg
  linarith

private lemma tlo_le_Tinf :
    tlo ≤ ∑' p : Nat.Primes, (Real.log (1 - 1/(p:Real)) + 1/(p:Real)) := by
  have hP2 : (∑ p ∈ Nat.primesLE 8192, (Real.log (1 - 1/(p:Real)) + 1/(p:Real))) ≤
      (∑' p : Nat.Primes, (Real.log (1 - 1/(p:Real)) + 1/(p:Real))) + 1/(8192:Real) := by
    have h := mertens_tail_upper_bound (x := (8192:Real)) (by norm_num)
    convert h using 1
    · norm_num
    · norm_num
  have hsub : Nat.primesLE 512 ⊆ Nat.primesLE 8192 := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hsplit : ∑ p ∈ Nat.primesLE 8192, (Real.log (1 - 1/(p:Real)) + 1/(p:Real)) =
      ∑ p ∈ Nat.primesLE 512, (Real.log (1 - 1/(p:Real)) + 1/(p:Real)) +
      ∑ p ∈ Nat.primesLE 8192 \ Nat.primesLE 512, (Real.log (1 - 1/(p:Real)) + 1/(p:Real)) := by
    rw [← Finset.sum_sdiff hsub, add_comm]
  have hW := WLO512_le_sum512
  have hm := hmid
  unfold tlo
  linarith

private lemma M_le_glo_tlo : M ≤ glo + tlo := by
  have h1 : (WLO 512 : Real) = ((-315600119/1000000000) : Real) := by
    have hq := WLO_512_val
    exact_mod_cast hq
  unfold M Mq glo tlo
  rw [h1]
  norm_num


private lemma T_eq_q : ∀ n, n ≤ 511 → (∑ p ∈ Nat.primesLE n, (1:Rat)/(p:Rat)) = T n := by
  intro n
  induction n with
  | zero => intro _; rw [show Nat.primesLE 0 = ∅ by simp [Nat.primesLE], show T 0 = (0/1:Rat) from rfl]; norm_num
  | succ k ih =>
    intro hk
    rw [sum_primesLE_succ k (fun p => (1:Rat)/(p:Rat)), ih (by omega), step_T_certificate k (by omega)]

private lemma T_eq (n : Nat) (hn : n ≤ 511) :
    (∑ p ∈ Nat.primesLE n, (1:Real)/(p:Real)) = (T n : Real) := by
  have h := congrArg (fun q : Rat => (q : Real)) (T_eq_q n hn)
  push_cast at h
  exact h


theorem mertens_reciprocal_endpoint_certificate_511 (n : Nat) (hn : 2 ≤ n) (hN : n ≤ 511) :
    (∑ p ∈ Nat.primesLE n, 1 / (p : Real)) ≤
      Real.log (Real.log (n : Real)) +
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : Real)) + 1 / (p : Real))) +
        4 / (Real.log ((n : Real) + 1)) ^ 3 := by
  have hTeq := T_eq n hN
  have hchk' := endpoint_certificate n hn hN
  have hchk'' : (T n : Real) ≤ (llb (lastP n) : Real) + (rho n : Real) +
      4/(lub (firstP n) : Real)^3 + (Mq : Real) := by exact_mod_cast hchk'
  have hrho := rho_le n hn hN
  have hM : (Mq : Real) ≤ glo + tlo := M_le_glo_tlo
  have hg := gamma_ge_glo
  have ht := tlo_le_Tinf
  calc (∑ p ∈ Nat.primesLE n, 1 / (p : Real))
      = (T n : Real) := hTeq
    _ ≤ (llb (lastP n) : Real) + (rho n : Real) + 4/(lub (firstP n) : Real)^3 + (Mq : Real) := hchk''
    _ ≤ Real.log (Real.log (n:Real)) + 4/(Real.log ((n:Real)+1))^3 + (glo + tlo) := by
        linarith
    _ ≤ Real.log (Real.log (n:Real)) + 4/(Real.log ((n:Real)+1))^3 +
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : Real)) + 1 / (p : Real))) := by
        linarith
    _ = Real.log (Real.log (n : Real)) +
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : Real)) + 1 / (p : Real))) +
        4 / (Real.log ((n : Real) + 1)) ^ 3 := by ring


end TaoFivePrimes

open TaoFivePrimes

theorem solution (n : Nat) (hn : 2 ≤ n) (hN : n ≤ 511) :
    (∑ p ∈ Nat.primesLE n, 1 / (p : Real)) ≤
      Real.log (Real.log (n : Real)) +
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : Real)) + 1 / (p : Real))) +
        4 / (Real.log ((n : Real) + 1)) ^ 3 :=
  TaoFivePrimes.mertens_reciprocal_endpoint_certificate_511 n hn hN
