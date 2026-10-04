-- Prove2me | solution 1 for PiIrrationality.zz_record_ratio
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T03:53:49.153157+00:00
-- url     : https://prove2.me/submissions/228362f9-6ebb-4f42-8f21-783f56f920b3

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

open Finset Real

set_option maxHeartbeats 0

lemma oddTerms_eq (x : ℝ) (M : ℕ) :
    (∑ i ∈ range (2 * M), (x ^ (i + 1) - (-x) ^ (i + 1)) / (i + 1 : ℝ)) =
      2 * ∑ m ∈ range M, x ^ (2 * m + 1) / (2 * m + 1 : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 2 by ring]
    rw [sum_range_succ, sum_range_succ, sum_range_succ, ih]
    have hodd : Odd (2 * M + 1) := odd_two_mul_add_one M
    have heven : Even (2 * M + 2) := ⟨M + 1, by ring⟩
    rw [hodd.neg_pow x, heven.neg_pow x]
    push_cast
    ring_nf

lemma log_ratio_approx {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (M : ℕ) :
    |log ((1 + x) / (1 - x)) -
        2 * ∑ m ∈ range M, x ^ (2 * m + 1) / (2 * m + 1 : ℝ)| ≤
      2 * x ^ (2 * M + 1) / (1 - x) := by
  have hxabs : |x| < 1 := by rwa [abs_of_pos hx]
  have hneg : |-x| < 1 := by rwa [abs_neg]
  let n := 2 * M
  have h1 := abs_log_sub_add_sum_range_le hxabs n
  have h2 := abs_log_sub_add_sum_range_le hneg n
  have hdiv : log ((1 + x) / (1 - x)) = log (1 + x) - log (1 - x) := by
    rw [log_div (by linarith) (by linarith)]
  set A := ∑ i ∈ range n, x ^ (i + 1) / (i + 1 : ℝ)
  set B := ∑ i ∈ range n, (-x) ^ (i + 1) / (i + 1 : ℝ)
  have hsplit : A - B = 2 * ∑ m ∈ range M, x ^ (2 * m + 1) / (2 * m + 1 : ℝ) := by
    have : A - B = ∑ i ∈ range n, (x ^ (i + 1) - (-x) ^ (i + 1)) / (i + 1 : ℝ) := by
      simp only [A, B, sum_sub_distrib, sub_div]
    simpa [n] using this.trans (oddTerms_eq x M)
  have hR : |x| ^ (n + 1) / (1 - |x|) = x ^ (2 * M + 1) / (1 - x) := by
    rw [abs_of_pos hx]
  have h1' : |A + log (1 - x)| ≤ x ^ (2 * M + 1) / (1 - x) := by simpa [A, hR] using h1
  have h2' : |B + log (1 + x)| ≤ x ^ (2 * M + 1) / (1 - x) := by
    simpa [B, hR, sub_neg_eq_add] using h2
  have herr :
      |log (1 + x) - log (1 - x) - (A - B)| ≤ 2 * x ^ (2 * M + 1) / (1 - x) := by
    have hsum := abs_sub_le (B + log (1 + x)) 0 (A + log (1 - x))
    simp only [sub_zero, zero_sub, abs_neg] at hsum
    have hre : (B + log (1 + x)) - (A + log (1 - x)) =
        log (1 + x) - log (1 - x) - (A - B) := by ring
    rw [← hre]
    have hmul : 2 * (x ^ (2 * M + 1) / (1 - x)) = 2 * x ^ (2 * M + 1) / (1 - x) := by ring
    linarith [hsum, h1', h2', hmul]
  rw [hdiv, ← hsplit]
  exact herr

lemma log_two_approx :
    |log 2 - 2 * ∑ m ∈ range 16, (1 / 3 : ℝ) ^ (2 * m + 1) / (2 * m + 1)| ≤
      (1 / 3) ^ 32 := by
  have h := log_ratio_approx (x := (1 : ℝ) / 3) (by norm_num) (by norm_num) 16
  have hratio : (1 + (1 : ℝ) / 3) / (1 - (1 : ℝ) / 3) = 2 := by norm_num
  rw [hratio] at h
  have herr : 2 * ((1 : ℝ) / 3) ^ (2 * 16 + 1) / (1 - (1 : ℝ) / 3) = ((1 : ℝ) / 3) ^ 32 := by
    norm_num
  rwa [herr] at h

lemma log_three_approx :
    |log 3 - 2 * ∑ m ∈ range 26, (1 / 2 : ℝ) ^ (2 * m + 1) / (2 * m + 1)| ≤
      (1 / 2) ^ 51 := by
  have h := log_ratio_approx (x := (1 : ℝ) / 2) (by norm_num) (by norm_num) 26
  have hratio : (1 + (1 : ℝ) / 2) / (1 - (1 : ℝ) / 2) = 3 := by norm_num
  rw [hratio] at h
  have herr : 2 * ((1 : ℝ) / 2) ^ (2 * 26 + 1) / (1 - (1 : ℝ) / 2) = ((1 : ℝ) / 2) ^ 51 := by
    norm_num
  rwa [herr] at h

lemma log_five_four_approx :
    |log ((5 : ℝ) / 4) - ∑ i ∈ range 30, ((1 : ℝ) / 5) ^ (i + 1) / (i + 1)| ≤
      (1 / 4) * ((1 : ℝ) / 5) ^ 30 := by
  have hx : |(1 : ℝ) / 5| < 1 := by norm_num
  have h := abs_log_sub_add_sum_range_le hx 30
  have herr :
      |(1 : ℝ) / 5| ^ (30 + 1) / (1 - |(1 : ℝ) / 5|) = (1 / 4) * ((1 : ℝ) / 5) ^ 30 := by
    norm_num
  rw [herr] at h
  have hlog : log ((5 : ℝ) / 4) = -log (1 - (1 : ℝ) / 5) := by
    have : ((5 : ℝ) / 4) = (1 - (1 : ℝ) / 5)⁻¹ := by norm_num
    rw [this, log_inv]
  have heq :
      log ((5 : ℝ) / 4) - ∑ i ∈ range 30, ((1 : ℝ) / 5) ^ (i + 1) / (i + 1) =
        -(∑ i ∈ range 30, ((1 : ℝ) / 5) ^ (i + 1) / (i + 1) + log (1 - (1 : ℝ) / 5)) := by
    rw [hlog]
    ring
  rw [heq, abs_neg]
  exact h

noncomputable def zzL : ℝ := (2185169139621 : ℝ) / 10 ^ 8

noncomputable def zzEps : ℝ := (13854115931 : ℝ) / 2199023255552

lemma log_eps_approx :
    |∑ i ∈ range 8, zzEps ^ (i + 1) / (i + 1) + log (1 - zzEps)| ≤
      zzEps ^ 9 / (1 - zzEps) := by
  have hx : |zzEps| < 1 := by unfold zzEps; norm_num
  have h := abs_log_sub_add_sum_range_le hx 8
  have hpos : 0 < zzEps := by unfold zzEps; norm_num
  rwa [abs_of_pos hpos] at h

lemma log_eps_err_le : zzEps ^ 9 / (1 - zzEps) ≤ (1 : ℝ) / 10 ^ 17 := by
  have hε : 0 < zzEps := by unfold zzEps; norm_num
  have hε1 : zzEps < (1 : ℝ) / 100 := by unfold zzEps; norm_num
  have hden : (1 : ℝ) / 2 ≤ 1 - zzEps := by unfold zzEps; norm_num
  have hpow : zzEps ^ 9 < ((1 : ℝ) / 100) ^ 9 :=
    pow_lt_pow_left₀ hε1 hε.le (by decide : 9 ≠ 0)
  have h100 : ((1 : ℝ) / 100) ^ 9 = 1 / 10 ^ 18 := by norm_num
  have hnum : zzEps ^ 9 < 1 / 10 ^ 18 := by rwa [h100] at hpow
  have hcmp : zzEps ^ 9 / (1 - zzEps) ≤ zzEps ^ 9 / ((1 : ℝ) / 2) :=
    div_le_div_of_nonneg_left (pow_nonneg hε.le 9) (by norm_num) hden
  have hhalf : zzEps ^ 9 / ((1 : ℝ) / 2) < (1 / 10 ^ 18) / ((1 : ℝ) / 2) :=
    div_lt_div_of_pos_right hnum (by norm_num)
  have hfin : (1 / 10 ^ 18) / ((1 : ℝ) / 2) = (2 : ℝ) / 10 ^ 18 := by norm_num
  have h17 : (2 : ℝ) / 10 ^ 18 ≤ 1 / 10 ^ 17 := by norm_num
  linarith

lemma log_zzL : log zzL = 17 * log 2 + log (1 - zzEps) - 8 * log ((5 : ℝ) / 4) := by
  have hL : zzL = (2 : ℝ) ^ 33 * (1 - zzEps) / (5 : ℝ) ^ 8 := by
    unfold zzL zzEps
    norm_num
  have hmul : (2 : ℝ) ^ 33 * (1 - zzEps) ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    unfold zzEps
    norm_num
  have h5 : (5 : ℝ) ^ 8 ≠ 0 := by norm_num
  rw [hL, log_div hmul h5]
  have h2 : (2 : ℝ) ^ 33 ≠ 0 := by norm_num
  have h1 : 1 - zzEps ≠ 0 := by unfold zzEps; norm_num
  rw [log_mul h2 h1, log_pow 2 33, log_pow 5 8]
  have hfive : log (5 : ℝ) = log ((5 : ℝ) / 4) + 2 * log 2 := by
    have : (5 : ℝ) = ((5 : ℝ) / 4) * 2 ^ 2 := by norm_num
    rw [this, log_mul (by norm_num) (by norm_num), log_pow 2 2]
    ring
  rw [hfive]
  ring

lemma sqrt3_bounds :
    (17320508075688772 : ℝ) / 10 ^ 16 ≤ sqrt 3 ∧
      sqrt 3 < (17320508075688773 : ℝ) / 10 ^ 16 := by
  have hlo : (17320508075688772 : ℝ) ^ 2 ≤ 3 * 10 ^ 32 := by norm_num
  have hhi : 3 * 10 ^ 32 < (17320508075688773 : ℝ) ^ 2 := by norm_num
  have hsq : (10 ^ 16 : ℝ) ^ 2 = 10 ^ 32 := by norm_num
  have h10 : (0 : ℝ) ≤ 10 ^ 16 := by norm_num
  have hdiv : sqrt (3 * 10 ^ 32) / 10 ^ 16 = sqrt 3 := by
    rw [← sqrt_sq h10, hsq, ← sqrt_div (by norm_num : (0 : ℝ) ≤ 3 * 10 ^ 32) (10 ^ 32)]
    congr 1
    norm_num
  constructor
  · have hs : (17320508075688772 : ℝ) ≤ sqrt (3 * 10 ^ 32) := by
      rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ (17320508075688772 : ℝ))]
      exact sqrt_le_sqrt hlo
    have : (17320508075688772 : ℝ) / 10 ^ 16 ≤ sqrt (3 * 10 ^ 32) / 10 ^ 16 :=
      div_le_div_of_nonneg_right hs (by norm_num)
    rwa [hdiv] at this
  · have hs : sqrt (3 * 10 ^ 32) < (17320508075688773 : ℝ) := by
      rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ (17320508075688773 : ℝ))]
      exact sqrt_lt_sqrt (by norm_num) hhi
    have : sqrt (3 * 10 ^ 32) / 10 ^ 16 < (17320508075688773 : ℝ) / 10 ^ 16 :=
      div_lt_div_of_pos_right hs (by norm_num)
    rwa [hdiv] at this

lemma sum_log_two_eq :
    2 * ∑ m ∈ range 16, ((1 : ℝ) / 3) ^ (2 * m + 1) / (2 * m + 1) = (10222343103897452720952704 : ℝ) / 14747723702258348925112275 := by
  norm_num

lemma sum_log_three_eq :
    2 * ∑ m ∈ range 26, ((1 : ℝ) / 2) ^ (2 * m + 1) / (2 * m + 1) = (9214647328847620885775278649548849 : ℝ) / 8387533458249311463840981555609600 := by
  norm_num

lemma sum_log_five_eq :
    ∑ i ∈ range 30, ((1 : ℝ) / 5) ^ (i + 1) / (i + 1) = (1257216089470559139639707640251 : ℝ) / 5634113475680351257324218750000 := by
  norm_num

lemma sum_log_eps_eq :
    ∑ i ∈ range 8, zzEps ^ (i + 1) / (i + 1) = (967647688373698647060638077563743035492000012560512940313547993328325590079447812277646835683145923 : ℝ) / 153107550734810834706075155898233495574721860162524870549803942448696709943956314625645922391613767680 := by
  unfold zzEps
  norm_num

noncomputable def l2Lo : ℝ := (10222343103897452720952704 : ℝ) / 14747723702258348925112275 - (1 : ℝ) / 1853020188851841
noncomputable def l2Hi : ℝ := (10222343103897452720952704 : ℝ) / 14747723702258348925112275 + (1 : ℝ) / 1853020188851841
noncomputable def l3Lo : ℝ := (9214647328847620885775278649548849 : ℝ) / 8387533458249311463840981555609600 - (1 : ℝ) / 2251799813685248
noncomputable def l3Hi : ℝ := (9214647328847620885775278649548849 : ℝ) / 8387533458249311463840981555609600 + (1 : ℝ) / 2251799813685248
noncomputable def l5Hi : ℝ := (1257216089470559139639707640251 : ℝ) / 5634113475680351257324218750000 + (1 : ℝ) / 3725290298461914062500
noncomputable def leLo : ℝ := -((967647688373698647060638077563743035492000012560512940313547993328325590079447812277646835683145923 : ℝ) / 153107550734810834706075155898233495574721860162524870549803942448696709943956314625645922391613767680) - 1 / 10 ^ 17
noncomputable def ellLo : ℝ := 17 * l2Lo + leLo - 8 * l5Hi
noncomputable def pLo : ℝ := (157079632679489661923 : ℝ) / 173205080756887730000
noncomputable def pHi : ℝ := (314159265358979323847 : ℝ) / 346410161513775440000

theorem solution (N : ℝ) (hL : (2185169139621 : ℝ) / 10 ^ 8 < N) :
    0 < (1 / 2) * Real.log N - 4 + Real.pi / (2 * Real.sqrt 3) ∧
      0 < Real.log N + 4 - (9 / 2) * Real.log 2 + (3 / 2) * Real.log 3 -
          Real.pi / (2 * Real.sqrt 3) ∧
        1 + (Real.log N + 4 - (9 / 2) * Real.log 2 + (3 / 2) * Real.log 3 -
              Real.pi / (2 * Real.sqrt 3)) /
            ((1 / 2) * Real.log N - 4 + Real.pi / (2 * Real.sqrt 3)) ≤
          7.103205334138 := by
  have hLdef : zzL = (2185169139621 : ℝ) / 10 ^ 8 := rfl
  rw [← hLdef] at hL
  set C0 : ℝ := (1 / 2) * log N - 4 + π / (2 * sqrt 3)
  set C1 : ℝ := log N + 4 - (9 / 2) * log 2 + (3 / 2) * log 3 - π / (2 * sqrt 3)
  set pterm : ℝ := π / (2 * sqrt 3)
  have hC0e : C0 = (1 / 2) * log N - 4 + pterm := by simp [C0, pterm]
  have hC1e : C1 = log N + 4 - (9 / 2) * log 2 + (3 / 2) * log 3 - pterm := by
    simp [C1, pterm]
  have h2 := log_two_approx
  rw [sum_log_two_eq] at h2
  have he2 : ((1 : ℝ) / 3) ^ 32 = (1 : ℝ) / 1853020188851841 := by norm_num
  rw [he2] at h2
  have h2lo : l2Lo ≤ log 2 := by
    have h := (abs_le.mp h2).1
    unfold l2Lo
    linarith
  have h2hi : log 2 ≤ l2Hi := by
    have h := (abs_le.mp h2).2
    unfold l2Hi
    linarith
  have h3 := log_three_approx
  rw [sum_log_three_eq] at h3
  have he3 : ((1 : ℝ) / 2) ^ 51 = (1 : ℝ) / 2251799813685248 := by norm_num
  rw [he3] at h3
  have h3lo : l3Lo ≤ log 3 := by
    have h := (abs_le.mp h3).1
    unfold l3Lo
    linarith
  have h3hi : log 3 ≤ l3Hi := by
    have h := (abs_le.mp h3).2
    unfold l3Hi
    linarith
  have h5 := log_five_four_approx
  rw [sum_log_five_eq] at h5
  have he5 : (1 / 4) * ((1 : ℝ) / 5) ^ 30 = (1 : ℝ) / 3725290298461914062500 := by norm_num
  rw [he5] at h5
  have h5hi : log ((5 : ℝ) / 4) ≤ l5Hi := by
    have h := (abs_le.mp h5).2
    unfold l5Hi
    linarith
  have heps := log_eps_approx
  rw [sum_log_eps_eq] at heps
  have heps_le : leLo ≤ log (1 - zzEps) := by
    have herr := log_eps_err_le
    have h := (abs_le.mp heps).1
    unfold leLo
    linarith
  have hlogL : ellLo ≤ log zzL := by
    rw [log_zzL]
    unfold ellLo
    linarith [h2lo, heps_le, h5hi]
  have hLpos : (0 : ℝ) < zzL := by unfold zzL; norm_num
  have hlogN : ellLo < log N := lt_of_le_of_lt hlogL (log_lt_log hLpos hL)
  have hsq := sqrt3_bounds
  have hpilo := pi_gt_d20
  have hpihi := pi_lt_d20
  have hp_lo : pLo < pterm := by
    have hden : 2 * sqrt 3 < 2 * ((17320508075688773 : ℝ) / 10 ^ 16) :=
      mul_lt_mul_of_pos_left hsq.2 (by norm_num)
    have hdenpos : (0 : ℝ) < 2 * sqrt 3 := mul_pos (by norm_num) (sqrt_pos.mpr (by norm_num))
    have hshipos : (0 : ℝ) < 2 * ((17320508075688773 : ℝ) / 10 ^ 16) := by norm_num
    have h1 : π / (2 * ((17320508075688773 : ℝ) / 10 ^ 16)) < π / (2 * sqrt 3) :=
      div_lt_div_of_pos_left pi_pos hdenpos hden
    have h2i : 3.14159265358979323846 / (2 * ((17320508075688773 : ℝ) / 10 ^ 16)) <
        π / (2 * ((17320508075688773 : ℝ) / 10 ^ 16)) :=
      div_lt_div_of_pos_right hpilo hshipos
    have hplo : pLo = 3.14159265358979323846 / (2 * ((17320508075688773 : ℝ) / 10 ^ 16)) := by
      unfold pLo
      norm_num
    unfold pterm
    rw [hplo]
    linarith
  have hp_hi : pterm < pHi := by
    have hden : 2 * ((17320508075688772 : ℝ) / 10 ^ 16) ≤ 2 * sqrt 3 :=
      mul_le_mul_of_nonneg_left hsq.1 (by norm_num)
    have hdlopos : (0 : ℝ) < 2 * ((17320508075688772 : ℝ) / 10 ^ 16) := by norm_num
    have h1 : π / (2 * sqrt 3) ≤ π / (2 * ((17320508075688772 : ℝ) / 10 ^ 16)) :=
      div_le_div_of_nonneg_left pi_pos.le hdlopos hden
    have h2i : π / (2 * ((17320508075688772 : ℝ) / 10 ^ 16)) <
        3.14159265358979323847 / (2 * ((17320508075688772 : ℝ) / 10 ^ 16)) :=
      div_lt_div_of_pos_right hpihi hdlopos
    have hphi : pHi = 3.14159265358979323847 / (2 * ((17320508075688772 : ℝ) / 10 ^ 16)) := by
      unfold pHi
      norm_num
    unfold pterm
    rw [hphi]
    linarith
  have hC0pos : 0 < C0 := by
    rw [hC0e]
    have hbase : 0 < (1 / 2) * ellLo - 4 + pLo := by
      unfold ellLo l2Lo leLo l5Hi pLo
      norm_num
    linarith [hlogN, hp_lo, hbase]
  have hC1pos : 0 < C1 := by
    rw [hC1e]
    have hbase : 0 < ellLo + 4 - (9 / 2) * l2Hi + (3 / 2) * l3Lo - pHi := by
      unfold ellLo l2Lo leLo l5Hi l2Hi l3Lo pHi
      norm_num
    linarith [hlogN, h2hi, h3lo, hp_hi, hbase]
  have hM : 0 < (7.103205334138 - 1) * C0 - C1 := by
    rw [hC0e, hC1e]
    have hid :
        (7.103205334138 - 1) * ((1 / 2) * log N - 4 + pterm) -
            (log N + 4 - (9 / 2) * log 2 + (3 / 2) * log 3 - pterm) =
          ((7.103205334138 - 1) / 2 - 1) * log N + 7.103205334138 * pterm +
            (9 / 2) * log 2 - (3 / 2) * log 3 - 4 * 7.103205334138 := by
      field_simp
      ring
    rw [hid]
    have hα : (0 : ℝ) < (7.103205334138 - 1) / 2 - 1 := by norm_num
    have hT : (0 : ℝ) < (7.103205334138 : ℝ) := by norm_num
    have hgrow :
        0 < ((7.103205334138 - 1) / 2 - 1) * (log N - ellLo) +
          7.103205334138 * (pterm - pLo) + (9 / 2) * (log 2 - l2Lo) +
          (3 / 2) * (l3Hi - log 3) := by
      have hA : 0 < ((7.103205334138 - 1) / 2 - 1) * (log N - ellLo) :=
        mul_pos hα (sub_pos.mpr hlogN)
      have hB : 0 < 7.103205334138 * (pterm - pLo) := mul_pos hT (sub_pos.mpr hp_lo)
      have hC : 0 ≤ (9 / 2) * (log 2 - l2Lo) := mul_nonneg (by norm_num) (sub_nonneg.mpr h2lo)
      have hD : 0 ≤ (3 / 2) * (l3Hi - log 3) := mul_nonneg (by norm_num) (sub_nonneg.mpr h3hi)
      linarith
    have hbase :
        0 ≤ ((7.103205334138 - 1) / 2 - 1) * ellLo + 7.103205334138 * pLo +
          (9 / 2) * l2Lo - (3 / 2) * l3Hi - 4 * 7.103205334138 := by
      unfold ellLo l2Lo leLo l5Hi l3Hi pLo
      norm_num
    linarith
  have hdiv : C1 / C0 < 7.103205334138 - 1 := by
    rw [div_lt_iff₀ hC0pos]
    linarith
  refine ⟨hC0pos, hC1pos, ?_⟩
  linarith
