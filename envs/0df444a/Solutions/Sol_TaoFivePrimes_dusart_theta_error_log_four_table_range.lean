-- Prove2me | solution 1 for TaoFivePrimes.dusart_theta_error_log_four_table_range
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-14T13:04:13.910103+00:00
-- url     : https://prove2.me/submissions/ffe1d499-3d96-449f-8f60-f94cec8aa0b6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Definitions.Def_DusartThetaTable1Intervals
import Theorems.Thm_TaoFivePrimes_dusart_theta_log_four_finite_mesh_certificate
import Theorems.Thm_TaoFivePrimes_dusart_table1_psi_bounds_for_log_four
import Theorems.Thm_TaoFivePrimes_dusart_theta_exponential_error

/- Adapted from Prove2Me accepted submission 32cd1a79-09ac-4589-8c61-5eddfe1c444c:
   replace its 24th Taylor term at u >= 49 by the 32nd term at u >= 40. -/

set_option maxHeartbeats 2000000


namespace DusartThetaReduction

lemma exp_dominates_ninth_power {u : ℝ} (hu : 40 ≤ u) : 18 * u ^ 9 ≤ Real.exp u := by
  have hu0 : 0 ≤ u := by linarith
  have hc : (18 : ℝ) * (Nat.factorial 32 : ℝ) ≤ 40 ^ 23 := by norm_num
  have hp : (18 : ℝ) * (Nat.factorial 32 : ℝ) ≤ u ^ 23 :=
    hc.trans (pow_le_pow_left₀ (by norm_num) hu 23)
  have hmul := mul_le_mul_of_nonneg_right hp (pow_nonneg hu0 9)
  have hfact : (0 : ℝ) < (Nat.factorial 32 : ℝ) := by positivity
  apply le_trans ((le_div_iff₀ hfact).mpr ?_) (Real.pow_div_factorial_le_exp u hu0 32)
  calc
    18 * u^9 * (Nat.factorial 32 : ℝ) = 18 * (Nat.factorial 32 : ℝ) * u^9 := by ring
    _ ≤ u^23*u^9 := hmul
    _ = u^32 := by ring

end DusartThetaReduction

theorem DusartThetaReduction.envelope_log_four_from_10000 (t : ℝ) (ht : 10000 ≤ t) :
    Real.sqrt (8 / Real.pi) *
      Real.sqrt (Real.sqrt (t / (569693 / 100000 : ℝ))) *
      Real.exp (-Real.sqrt (t / (569693 / 100000 : ℝ))) ≤
      (1513 / 10 : ℝ) / t ^ 4 := by
  let R : ℝ := 569693 / 100000
  let u : ℝ := Real.sqrt (t / R)
  have hR : 0 < R := by norm_num [R]
  have hR6 : R ≤ 6 := by norm_num [R]
  have ht0 : 0 < t := by linarith
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have husq : u ^ 2 = t / R := Real.sq_sqrt (div_nonneg ht0.le hR.le)
  have hu40 : 40 ≤ u := by
    have hh : (40 : ℝ)^2 ≤ t/R := (le_div_iff₀ hR).mpr (by norm_num [R]; linarith)
    nlinarith
  have ht_scale : t = R * u^2 := by rw [husq, mul_div_cancel₀ _ hR.ne']
  have ht_le : t ≤ 6*u^2 := by rw [ht_scale]; nlinarith [sq_nonneg u]
  have ht4 : t^4 ≤ 6^4*u^8 := by
    have h := pow_le_pow_left₀ ht0.le ht_le 4
    simpa only [mul_pow, ← pow_mul] using h
  have hpi : Real.sqrt (8/Real.pi) ≤ 2 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.two_le_pi]
  have hsqrt : Real.sqrt u ≤ u := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hexp := DusartThetaReduction.exp_dominates_ninth_power hu40
  have hden : 0 < 18*u^9 := by positivity
  have hinv : Real.exp (-u) ≤ 1/(18*u^9) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hden hexp
  change Real.sqrt (8/Real.pi) * Real.sqrt u * Real.exp (-u) ≤ (1513/10:ℝ)/t^4
  calc
    _ ≤ (2*u)*Real.exp (-u) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hpi hsqrt (Real.sqrt_nonneg u) (by norm_num)) (Real.exp_pos _).le
    _ ≤ (2*u)/(18*u^9) := by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 2*u)
    _ ≤ (1513/10:ℝ)/t^4 := by
      apply (div_le_div_iff₀ hden (pow_pos ht0 4)).mpr
      have h := mul_le_mul_of_nonneg_left ht4 (by positivity : 0 ≤ 2*u)
      nlinarith [pow_nonneg hu0 9]

set_option maxHeartbeats 4000000

noncomputable section
namespace DusartThetaReduction

/-- An explicit elementary replacement for the sharper prime-power gap. -/
lemma psi_theta_gap_eighteen (x : ℝ) (hx : 1 ≤ x) :
    |Chebyshev.psi x - Chebyshev.theta x| ≤ 18 * Real.sqrt x := by
  have hp (n : ℕ) (hn : 2 ≤ n) :
      Chebyshev.psi (x ^ (1 / (n : ℝ))) ≤ (Real.log 4 + 4) * Real.sqrt x := by
    apply (Chebyshev.psi_le_const_mul_self (by positivity)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_le hx
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hn)
  have hs := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have he : (2 : ℝ)⁻¹ = 1 / 2 := by ring
  have he3 : (3 : ℝ)⁻¹ = 1 / 3 := by ring
  have he5 : (5 : ℝ)⁻¹ = 1 / 5 := by ring
  rw [he, he3, he5] at hs
  have hlog : Real.log 4 ≤ 2 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    exact (Real.log_le_iff_le_exp (by norm_num)).2 (by linarith)
  have hm := mul_le_mul_of_nonneg_right hlog (Real.sqrt_nonneg x)
  rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))]
  linarith [hp 2 (by norm_num), hp 3 (by norm_num), hp 5 (by norm_num)]

def taylorLower (b : ℕ) : ℚ :=
  ∑ k ∈ Finset.range 31, ((b : ℚ) / 2)^k / (Nat.factorial k : ℚ)

def rowCheck (r : DusartThetaTable.Row) : Prop :=
  23 ≤ r.b ∧ r.b < r.next ∧ 0 ≤ r.epsilon ∧ 0 < taylorLower r.b ∧
    (r.epsilon + 18 / taylorLower r.b) * (r.next : ℚ)^4 ≤ (1513 / 10 : ℚ)

lemma all_row_checks (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows) : rowCheck r := by
  simp only [DusartThetaTable.rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [rowCheck, taylorLower, Finset.sum_range_succ, Nat.factorial]

lemma taylorLower_le_exp (b : ℕ) : (taylorLower b : ℝ) ≤ Real.exp ((b : ℝ) / 2) := by
  unfold taylorLower
  push_cast
  exact Real.sum_le_exp_of_nonneg (by positivity) 31

lemma row_gaussian_gap_margin (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows) :
    ((r.epsilon : ℝ) + 18 * Real.exp (-(r.b : ℝ) / 2)) * (r.next : ℝ)^4 ≤ (1513 / 10 : ℝ) := by
  have hc := all_row_checks r hr
  have hp : (0 : ℝ) < (taylorLower r.b : ℝ) := by exact_mod_cast hc.2.2.2.1
  have hn : ((r.epsilon : ℝ) + 18 / (taylorLower r.b : ℝ)) * (r.next : ℝ)^4 ≤ (1513 / 10 : ℝ) := by
    have hRat := hc.2.2.2.2
    have hcast : (((r.epsilon + 18 / taylorLower r.b) * (r.next : ℚ)^4 : ℚ) : ℝ) ≤
        ((1513 / 10 : ℚ) : ℝ) := Rat.cast_le.mpr hRat
    push_cast at hcast
    exact hcast
  have hi : Real.exp (-(r.b : ℝ) / 2) ≤ 1 / (taylorLower r.b : ℝ) := by
    rw [show -(r.b : ℝ) / 2 = -((r.b : ℝ) / 2) by ring, Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hp (taylorLower_le_exp r.b)
  have hm := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 18)
  have hsum : (r.epsilon : ℝ) + 18 * Real.exp (-(r.b : ℝ) / 2) ≤
      (r.epsilon : ℝ) + 18 / (taylorLower r.b : ℝ) := by
    rw [mul_one_div] at hm
    exact add_le_add le_rfl hm
  exact (mul_le_mul_of_nonneg_right hsum (pow_nonneg (Nat.cast_nonneg r.next) 4)).trans hn

lemma table_covers (t : ℝ) (hl : 23 ≤ t) (hu : t ≤ 10000) :
    ∃ r ∈ DusartThetaTable.rows, (r.b : ℝ) ≤ t ∧ t ≤ (r.next : ℝ) := by
  by_cases h24 : t ≤ 24
  · exact ⟨⟨23, 24, 2431 / 10^7⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h25 : t ≤ 25
  · exact ⟨⟨24, 25, 1496 / 10^7⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h30 : t ≤ 30
  · exact ⟨⟨25, 30, 9250 / 10^8⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h35 : t ≤ 35
  · exact ⟨⟨30, 35, 9647 / 10^9⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h40 : t ≤ 40
  · exact ⟨⟨35, 40, 1078 / 10^9⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h45 : t ≤ 45
  · exact ⟨⟨40, 45, 1161 / 10^10⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h50 : t ≤ 50
  · exact ⟨⟨45, 50, 1225 / 10^11⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h55 : t ≤ 55
  · exact ⟨⟨50, 55, 1275 / 10^12⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h60 : t ≤ 60
  · exact ⟨⟨55, 60, 1388 / 10^13⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h65 : t ≤ 65
  · exact ⟨⟨60, 65, 2978 / 10^14⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h70 : t ≤ 70
  · exact ⟨⟨65, 70, 2039 / 10^14⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h75 : t ≤ 75
  · exact ⟨⟨70, 75, 1940 / 10^14⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h80 : t ≤ 80
  · exact ⟨⟨75, 80, 1913 / 10^14⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h85 : t ≤ 85
  · exact ⟨⟨80, 85, 1893 / 10^14⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h90 : t ≤ 90
  · exact ⟨⟨85, 90, 1868 / 10^14⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h95 : t ≤ 95
  · exact ⟨⟨90, 95, 1847 / 10^14⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h100 : t ≤ 100
  · exact ⟨⟨95, 100, 1830 / 10^14⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h200 : t ≤ 200
  · exact ⟨⟨100, 200, 1815 / 10^14⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h300 : t ≤ 300
  · exact ⟨⟨200, 300, 1557 / 10^14⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h400 : t ≤ 400
  · exact ⟨⟨300, 400, 1404 / 10^14⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h500 : t ≤ 500
  · exact ⟨⟨400, 500, 1288 / 10^14⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h600 : t ≤ 600
  · exact ⟨⟨500, 600, 1215 / 10^14⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h700 : t ≤ 700
  · exact ⟨⟨600, 700, 1115 / 10^14⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h800 : t ≤ 800
  · exact ⟨⟨700, 800, 1039 / 10^14⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h900 : t ≤ 900
  · exact ⟨⟨800, 900, 9826 / 10^15⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h1000 : t ≤ 1000
  · exact ⟨⟨900, 1000, 9281 / 10^15⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h1500 : t ≤ 1500
  · exact ⟨⟨1000, 1500, 8743 / 10^15⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h2000 : t ≤ 2000
  · exact ⟨⟨1500, 2000, 5311 / 10^15⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h2500 : t ≤ 2500
  · exact ⟨⟨2000, 2500, 2536 / 10^15⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h3000 : t ≤ 3000
  · exact ⟨⟨2500, 3000, 8941 / 10^16⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h3500 : t ≤ 3500
  · exact ⟨⟨3000, 3500, 3156 / 10^16⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h4000 : t ≤ 4000
  · exact ⟨⟨3500, 4000, 1116 / 10^16⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h4500 : t ≤ 4500
  · exact ⟨⟨4000, 4500, 3946 / 10^17⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h5000 : t ≤ 5000
  · exact ⟨⟨4500, 5000, 1274 / 10^17⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h6000 : t ≤ 6000
  · exact ⟨⟨5000, 6000, 3956 / 10^18⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h7000 : t ≤ 7000
  · exact ⟨⟨6000, 7000, 4893 / 10^19⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h8000 : t ≤ 8000
  · exact ⟨⟨7000, 8000, 6393 / 10^20⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  by_cases h9000 : t ≤ 9000
  · exact ⟨⟨8000, 9000, 8969 / 10^21⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩
  exact ⟨⟨9000, 10000, 2427 / 10^21⟩, by simp [DusartThetaTable.rows], by norm_num; linarith, by norm_num; linarith⟩

end DusartThetaReduction
end

set_option maxHeartbeats 1000000
noncomputable section
namespace DusartThetaReduction

lemma theta_constant_mesh (n : ℕ) (x : ℝ)
    (ha : (n : ℝ) / 16 ≤ x) (hb : x < ((n : ℝ) + 1) / 16) :
    Chebyshev.theta x = Chebyshev.theta ((n : ℝ) / 16) := by
  let k : ℕ := n / 16
  have hlow : k * 16 ≤ n := Nat.div_mul_le_self n 16
  have hupp : n + 1 ≤ (k + 1) * 16 := by dsimp [k]; omega
  have hlowR : (k : ℝ) * 16 ≤ (n : ℝ) := by exact_mod_cast hlow
  have huppR : (n : ℝ) + 1 ≤ ((k : ℝ) + 1) * 16 := by exact_mod_cast hupp
  have hfa : Nat.floor ((n : ℝ) / 16) = k :=
    (Nat.floor_eq_iff (by positivity : 0 ≤ (n : ℝ) / 16)).2 ⟨by linarith, by linarith⟩
  have hfx : Nat.floor x = k :=
    (Nat.floor_eq_iff (show 0 ≤ x by have hn := Nat.cast_nonneg (α := ℝ) n; linarith)).2
      ⟨by linarith, by linarith⟩
  rw [Chebyshev.theta_eq_theta_coe_floor x, Chebyshev.theta_eq_theta_coe_floor ((n : ℝ) / 16), hfx, hfa]

lemma small_range_of_mesh_certificate (x : ℝ) (hx : 2 ≤ x) (hsmall : x ≤ Real.exp 23) :
    |Chebyshev.theta x - x| ≤ (1513 / 10 : ℝ) * x / (Real.log x)^4 := by
  let n : ℕ := Nat.floor (16 * x)
  have hx0 : 0 ≤ 16 * x := by linarith
  have hnl : (n : ℝ) ≤ 16 * x := Nat.floor_le hx0
  have hnu : 16 * x < (n : ℝ) + 1 := Nat.lt_floor_add_one (16 * x)
  have hn : 32 ≤ n := by
    apply (Nat.le_floor_iff hx0).2
    norm_num
    linarith
  have hcap : n ≤ Nat.ceil (16 * Real.exp 23) := by
    apply Nat.floor_le_of_le
    exact (mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 16)).trans (Nat.le_ceil _)
  have ha : (n : ℝ) / 16 ≤ x := by linarith
  have hb : x < ((n : ℝ) + 1) / 16 := by linarith
  have han : 2 ≤ (n : ℝ) / 16 := by have h := (show (32 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn); linarith
  have hab : (n : ℝ) / 16 ≤ ((n : ℝ) + 1) / 16 := by linarith
  have hc := TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate n hn hcap
  dsimp only at hc
  have he := theta_constant_mesh n x ha hb
  rw [he]
  have hB : |Chebyshev.theta ((n : ℝ) / 16) - x| ≤
      (1513 / 10 : ℝ) * ((n : ℝ) / 16) / (Real.log (((n : ℝ) + 1) / 16))^4 := by
    apply abs_le.mpr
    have hl := (abs_le.mp hc.1).2
    have hu := (abs_le.mp hc.2).1
    constructor <;> linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogb : 0 < Real.log (((n : ℝ) + 1) / 16) := Real.log_pos (by linarith)
  apply hB.trans
  apply div_le_div₀ (by positivity : (0 : ℝ) ≤ (1513 / 10) * x)
    (mul_le_mul_of_nonneg_left ha (by norm_num : (0 : ℝ) ≤ 1513 / 10))
    (pow_pos hlogx 4)
  exact pow_le_pow_left₀ hlogx.le (Real.log_le_log (by linarith : 0 < x) hb.le) 4

end DusartThetaReduction
end

set_option maxHeartbeats 4000000
noncomputable section
namespace DusartThetaReduction

lemma theta_bound_of_row (x : ℝ) (hx : 2 ≤ x) (r : DusartThetaTable.Row)
    (hr : r ∈ DusartThetaTable.rows)
    (hlo : (r.b : ℝ) ≤ Real.log x) (hhi : Real.log x ≤ (r.next : ℝ)) :
    |Chebyshev.theta x - x| ≤ (1513 / 10 : ℝ) * x / (Real.log x)^4 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hxe : Real.exp (r.b : ℝ) ≤ x := by
    rw [← Real.exp_log hx0]
    exact Real.exp_le_exp.mpr hlo
  have hpsi := TaoFivePrimes.dusart_table1_psi_bounds_for_log_four r hr x hxe
  have hgap := psi_theta_gap_eighteen x hx1
  have hsqrt : Real.sqrt x ≤ x * Real.exp (-(r.b : ℝ) / 2) := by
    rw [← Real.exp_log hx0, ← Real.exp_add, ← Real.exp_half]
    exact Real.exp_le_exp.mpr (by linarith)
  have htri : |Chebyshev.theta x - x| ≤
      |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := by
    have h := abs_add_le (Chebyshev.psi x - x) (Chebyshev.theta x - Chebyshev.psi x)
    rw [show Chebyshev.psi x - x + (Chebyshev.theta x - Chebyshev.psi x) =
      Chebyshev.theta x - x by ring] at h
    simpa only [abs_sub_comm (Chebyshev.theta x) (Chebyshev.psi x)] using h
  have hmul := mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ) ≤ 18)
  have hsum : |Chebyshev.theta x - x| ≤
      x * ((r.epsilon : ℝ) + 18 * Real.exp (-(r.b : ℝ) / 2)) := by
    nlinarith only [htri, hpsi, hgap, hmul]
  have hn : (0 : ℝ) ≤ (r.epsilon : ℝ) := by
    exact_mod_cast (all_row_checks r hr).2.2.1
  have hc : 0 ≤ (r.epsilon : ℝ) + 18 * Real.exp (-(r.b : ℝ) / 2) := by positivity
  have hpow := pow_le_pow_left₀ hlog.le hhi 4
  have hM := (mul_le_mul_of_nonneg_left hpow hc).trans (row_gaussian_gap_margin r hr)
  have hfrac : (r.epsilon : ℝ) + 18 * Real.exp (-(r.b : ℝ) / 2) ≤
      (1513 / 10 : ℝ) / (Real.log x)^4 := (le_div_iff₀ (pow_pos hlog 4)).2 hM
  have ht := mul_le_mul_of_nonneg_left hfrac hx0.le
  exact hsum.trans (ht.trans_eq (by ring))

end DusartThetaReduction
end

theorem solution (x : ℝ) (hx : 2 ≤ x) (_hupper : x ≤ Real.exp 13900) :
    |Chebyshev.theta x - x| ≤ (1513 / 10 : ℝ) * x / (Real.log x)^4 := by
  have hx0 : 0 < x := by linarith
  by_cases hbig : 10000 ≤ Real.log x
  · have h := (TaoFivePrimes.dusart_theta_exponential_error x hx0 (by norm_num; linarith)).le
    have hc := mul_le_mul_of_nonneg_left
      (DusartThetaReduction.envelope_log_four_from_10000 (Real.log x) hbig) hx0.le
    calc
      _ ≤ x * (Real.sqrt (8 / Real.pi) *
        Real.sqrt (Real.sqrt (Real.log x / (569693 / 100000 : ℝ))) *
        Real.exp (-Real.sqrt (Real.log x / (569693 / 100000 : ℝ)))) := by
        simpa only [mul_assoc] using h
      _ ≤ x * ((1513 / 10 : ℝ) / (Real.log x)^4) := hc
      _ = _ := by ring
  · by_cases hsmall : x ≤ Real.exp 23
    · exact DusartThetaReduction.small_range_of_mesh_certificate x hx hsmall
    · have hlo : 23 ≤ Real.log x := by
        have h := Real.log_le_log (Real.exp_pos 23) (le_of_not_ge hsmall)
        simpa only [Real.log_exp] using h
      obtain ⟨r, hr, hl, hu⟩ := DusartThetaReduction.table_covers (Real.log x) hlo (le_of_not_ge hbig)
      exact DusartThetaReduction.theta_bound_of_row x hx r hr hl hu
