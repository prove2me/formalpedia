-- Prove2me | solution 1 for QMC0614.ratio_gt_0611
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T14:56:19.07306+00:00
-- url     : https://prove2.me/submissions/d92aab14-3e5d-4eea-bb10-6843e65f379a

import Mathlib
import Definitions.Def_QuantumMaxCutBFVProductRounding

set_option autoImplicit false
open scoped BigOperators

/-!
# The three-parameter min-max endgame of the 0.611 quantum max-cut analysis

Per-edge analysis of ALMPS25 (arXiv:2504.15276) Section 4.2: the mixture of MATCH and PMATCH
energies dominates `0.611` times the SDP bound on every edge with Pauli correlation
`s ∈ [-1, 1/3)`, at the certified point `μ = 0.861`, `sin θ = 0.28086` (paper: `θ = 0.2845`),
with matching weight `d = 1` (the augmented-SDP case).
-/

namespace QMC0614
open BFVBound

/-! ## Series bounds for the BFV hypergeometric factor -/

lemma poch_two_pos : ∀ n, 0 < poch 2 n := by
  intro n
  induction n with
  | zero => norm_num [poch]
  | succ n ih => rw [poch]; positivity

lemma poch_half_pos : ∀ n, 0 < poch (1 / 2) n := by
  intro n
  induction n with
  | zero => norm_num [poch]
  | succ n ih => rw [poch]; positivity

lemma poch_half_nonneg (n : ℕ) : 0 ≤ poch (1 / 2) n := (poch_half_pos n).le

lemma factorial_ne_zero (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by
  exact_mod_cast n.factorial_ne_zero

lemma coeff_nonneg (n : ℕ) : 0 ≤ coeff n := by
  unfold coeff
  have h := poch_two_pos n
  have h2 := poch_half_nonneg n
  positivity

lemma coeff_zero : coeff 0 = 1 := by simp [coeff, poch]

lemma coeff_one : coeff 1 = 1 / 8 := by
  norm_num [coeff, poch, Nat.factorial]

lemma coeff_succ (n : ℕ) :
    coeff (n + 1) = coeff n * ((n + 1 / 2) ^ 2 / ((n + 2) * (n + 1))) := by
  have h1 : poch (1 / 2) (n + 1) = poch (1 / 2) n * (n + 1 / 2) := by
    rw [poch]; ring
  have h2 : poch 2 (n + 1) = poch 2 n * (n + 2) := by
    rw [poch]; ring
  have hf : (((n + 1).factorial : ℕ) : ℝ) = (n.factorial : ℝ) * ((n : ℝ) + 1) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hp : (poch 2 n : ℝ) ≠ 0 := ne_of_gt (poch_two_pos n)
  have hf' : (n.factorial : ℝ) ≠ 0 := factorial_ne_zero n
  unfold coeff
  rw [h1, h2, hf]
  field_simp

private lemma coeff_le' (n : ℕ) : coeff n ≤ 2 / (((n:ℝ)+1) * ((n:ℝ)+2)) := by
  induction n with
  | zero => rw [coeff_zero]; norm_num
  | succ n ih =>
    have hcoeff : coeff (n+1) =
        coeff n * (((n:ℝ) + 1/2)^2 / (((n:ℝ)+2) * ((n:ℝ)+1))) := by
      rw [coeff_succ]
    rw [hcoeff]
    have hstep : ((n:ℝ) + 1/2)^2 / (((n:ℝ)+2) * ((n:ℝ)+1)) ≤ ((n:ℝ)+1) / ((n:ℝ)+3) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg ((n:ℝ) + 1/2)]
    have hA : (0:ℝ) ≤ ((n:ℝ) + 1/2)^2 / (((n:ℝ)+2) * ((n:ℝ)+1)) :=
      div_nonneg (sq_nonneg _) (by positivity)
    have hB : (0:ℝ) ≤ 2 / (((n:ℝ)+1) * ((n:ℝ)+2)) := by positivity
    have hprod := mul_le_mul ih hstep hA hB
    have hgoal : (2 / (((n:ℝ)+1) * ((n:ℝ)+2))) * (((n:ℝ)+1) / ((n:ℝ)+3))
        = 2 / ((↑(n+1) + 1) * (↑(n+1) + 2)) := by
      push_cast
      field_simp
      ring
    calc coeff n * (((n:ℝ) + 1/2)^2 / (((n:ℝ)+2) * ((n:ℝ)+1)))
        ≤ (2 / (((n:ℝ)+1) * ((n:ℝ)+2))) * (((n:ℝ)+1) / ((n:ℝ)+3)) := hprod
      _ = 2 / ((↑(n+1) + 1) * (↑(n+1) + 2)) := hgoal

lemma coeff_le (n : ℕ) : coeff n ≤ 2 / ((n + 1) * (n + 2)) := coeff_le' n

lemma summable_telescope : Summable (fun n : ℕ => (2:ℝ) / ((n + 1) * (n + 2))) := by
  refine summable_of_sum_range_le (f := fun n : ℕ => (2:ℝ) / ((n + 1) * (n + 2))) (c := 2) (fun n => by positivity) (fun n => ?_)
  have h : (∑ i ∈ Finset.range n, (2:ℝ) / ((i + 1) * (i + 2))) = 2 - 2 / ((n:ℝ) + 1) := by
    induction n with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; field_simp; ring
  rw [h]
  have hpos : (0:ℝ) ≤ 2 / ((n:ℝ) + 1) := by positivity
  linarith

lemma summable_coeff_mul (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    Summable (fun n : ℕ => coeff n * x ^ n) := by
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (coeff_nonneg n) (pow_nonneg hx0 n)) (fun n => ?_) summable_telescope
  have h1 : x ^ n ≤ 1 := by
    calc x ^ n ≤ 1 ^ n := pow_le_pow_left₀ hx0 hx1 n
      _ = 1 := one_pow n
  calc coeff n * x ^ n ≤ (2 / ((n+1)*(n+2))) * 1 := by
        apply mul_le_mul (coeff_le n) h1 (by positivity) (by positivity)
    _ = 2 / ((n+1)*(n+2)) := mul_one _

lemma G_ge (x : ℝ) (hx : x ∈ Set.Icc 0 1) : 1 + x / 8 ≤ G x := by
  have hs := summable_coeff_mul x hx
  have h2 : (∑ n ∈ Finset.range 2, coeff n * x ^ n) ≤ G x :=
    hs.sum_le_tsum (Finset.range 2) (fun n _ => mul_nonneg (coeff_nonneg n) (pow_nonneg hx.1 n))
  have hval : (∑ n ∈ Finset.range 2, coeff n * x ^ n) = 1 + x / 8 := by
    simp [Finset.sum_range_succ, coeff_zero, coeff_one]
    ring
  linarith [hval ▸ h2]

lemma c_ge : (0.8488 : ℝ) ≤ 8 / (3 * Real.pi) := by
  rw [le_div_iff₀ (by positivity)]
  have hpi : Real.pi ≤ 3.141593 := le_of_lt (lt_trans Real.pi_lt_d20 (by norm_num))
  nlinarith [Real.pi_gt_three]

lemma c_le : 8 / (3 * Real.pi) ≤ 8 / 9 := by
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [Real.pi_gt_three]

/-- The hypergeometric coefficients are at most `1`. -/
lemma coeff_le_one : ∀ n, coeff n ≤ 1 := by
  intro n
  induction n with
  | zero => rw [coeff_zero]
  | succ n ih =>
    rw [coeff_succ]
    have hnn : (0:ℝ) ≤ coeff n := coeff_nonneg n
    have hratio : ((n:ℝ) + 1/2)^2 / (((n:ℝ)+2) * ((n:ℝ)+1)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [sq_nonneg ((n:ℝ) + 1/2)]
    calc coeff n * ((n + 1/2)^2 / ((n + 2) * (n + 1)))
        ≤ 1 * 1 := by
          apply mul_le_mul ih hratio ?_ ?_
          · exact div_nonneg (sq_nonneg _) (by positivity)
          · exact zero_le_one
      _ = 1 := mul_one 1

/-- `G` is dominated by the geometric series: `G x ≤ 1/(1-x)` on `[0,1)`. -/
lemma G_le_geom (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) : G x ≤ 1 / (1 - x) := by
  have hsum : Summable (fun n : ℕ => x ^ n) := summable_geometric_of_lt_one h0 h1
  have hcoef : Summable (fun n : ℕ => coeff n * x ^ n) :=
    summable_coeff_mul x ⟨h0, le_of_lt h1⟩
  have hle : (∑' n, coeff n * x ^ n) ≤ ∑' n, x ^ n := by
    refine Summable.tsum_le_tsum (f := fun n => coeff n * x ^ n) (g := fun n => x ^ n) (fun n => ?_) hcoef hsum
    have hx : (0:ℝ) ≤ x ^ n := pow_nonneg h0 n
    calc coeff n * x ^ n ≤ 1 * x ^ n := mul_le_mul_of_nonneg_right (coeff_le_one n) hx
      _ = x ^ n := one_mul _
  calc G x = ∑' n, coeff n * x ^ n := rfl
    _ ≤ ∑' n, x ^ n := hle
    _ = (1 - x)⁻¹ := tsum_geometric_of_lt_one h0 h1
    _ = 1 / (1 - x) := by rw [one_div]

/-- Upper bound on the product side, positive range: `F s ≤ s` on `[0, 1/3]`. -/
lemma F_le_self (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1 / 3) : F s ≤ s := by
  have hs2 : s ^ 2 ∈ Set.Icc (0:ℝ) 1 := ⟨by positivity, by nlinarith⟩
  have hlt : s ^ 2 < 1 := by nlinarith
  have hG := G_le_geom (s ^ 2) (by positivity) hlt
  have hGpos : (0:ℝ) < G (s ^ 2) := lt_of_lt_of_le (by positivity) (G_ge (s ^ 2) hs2)
  have hden : (0:ℝ) < 1 - s ^ 2 := by nlinarith
  have h1m : 1 / (1 - s ^ 2) ≤ 9 / 8 := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hc : 8 / (3 * Real.pi) ≤ 8 / 9 := c_le
  have hmain : (8 / (3 * Real.pi)) * G (s ^ 2) ≤ (8 / 9) * (9 / 8) := by
    apply mul_le_mul hc (le_trans hG h1m) hGpos.le (by norm_num)
  calc F s = (8 / (3 * Real.pi)) * s * G (s ^ 2) := rfl
    _ = s * ((8 / (3 * Real.pi)) * G (s ^ 2)) := by ring
    _ ≤ s * ((8 / 9) * (9 / 8)) := by
        apply mul_le_mul_of_nonneg_left _ h0
        simpa using hmain
    _ = s := by ring

/-- Upper bound on the product side, negative range: for `s ∈ [-1, 0]`,
`F s ≤ 0.8488 · s · (1 + s²/8)` (recall `F s < 0` there). -/
lemma F_le_neg (s : ℝ) (hs1 : -1 ≤ s) (hs0 : s ≤ 0) :
    F s ≤ 0.8488 * s * (1 + s ^ 2 / 8) := by
  have hx : s ^ 2 ∈ Set.Icc (0:ℝ) 1 := ⟨by positivity, by nlinarith⟩
  have hG := G_ge (s ^ 2) hx
  have hc := c_ge
  have h1 : 0.8488 * (1 + s ^ 2 / 8) ≤ (8 / (3 * Real.pi)) * G (s ^ 2) := by
    have hnn : (0:ℝ) ≤ 1 + s ^ 2 / 8 := by positivity
    calc 0.8488 * (1 + s ^ 2 / 8) ≤ (8 / (3 * Real.pi)) * (1 + s ^ 2 / 8) :=
          mul_le_mul_of_nonneg_right hc hnn
      _ ≤ (8 / (3 * Real.pi)) * G (s ^ 2) := mul_le_mul_of_nonneg_left hG (by positivity)
  calc F s = (8 / (3 * Real.pi)) * s * G (s ^ 2) := rfl
    _ = s * ((8 / (3 * Real.pi)) * G (s ^ 2)) := by ring
    _ ≤ s * (0.8488 * (1 + s ^ 2 / 8)) := mul_le_mul_of_nonpos_left h1 hs0
    _ = 0.8488 * s * (1 + s ^ 2 / 8) := by ring

end QMC0614

open QMC0614 BFVBound

/-- **The three-parameter min-max endgame at `d = 1`.** At the certified point `μ = 0.861`,
`sin θ = 0.28086` (i.e. `θ ≈ 0.2847`, the paper's point) and `d = 14/15` the mixture of the MATCH and PMATCH
per-edge energies exceeds `0.611` times the SDP bound, on the whole range
`s ∈ [-1, 1/3)` of Pauli correlations. -/
theorem solution (s : ℝ) (h1 : -1 ≤ s) (h2 : s < 1 / 3) :
    (0.611 : ℝ) < QMC0614.mixture (14 / 15) 0.861 0.28086 s := by
  have hden : (0:ℝ) < 1 - 3 * s := by linarith
  have hmix : mixture (14 / 15) 0.861 0.28086 s
      = (0.861 * (1 - F s * (1 - 0.28086 ^ 2) + (14 / 15) * 0.28086 * (1 - F s * (1 + 0.28086)) *
          max (-(1 + 3 * s) / 2) 0)
        + (1 - 0.861) * (1 + 3 * (14 / 15) * max (-(1 + 3 * s) / 2) 0)) / (1 - 3 * s) := by
    unfold mixture EPM EM
    field_simp
  rw [hmix, lt_div_iff₀ hden]
  rcases le_or_gt (-1 / 3 : ℝ) s with hA | hA
  · -- `s ≥ -1/3`: the matching bracket vanishes
    have hmax : max (-(1 + 3 * s) / 2) 0 = 0 := max_eq_right (by linarith)
    rw [hmax]
    simp only [mul_zero, add_zero]
    rcases le_or_gt (0:ℝ) s with hs0 | hs0
    · -- `s ≥ 0`: `F s ≤ s`
      have hF : F s ≤ s := F_le_self s hs0 (le_of_lt h2)
      nlinarith [hF]
    · -- `s < 0`: `F s ≤ 0.8488 s`
      have hF₀ : F s ≤ 0.8488 * s * (1 + s ^ 2 / 8) := F_le_neg s h1 hs0.le
      have hF : F s ≤ 0.8488 * s := by nlinarith [hF₀, sq_nonneg s]
      nlinarith [hF]
  · -- `s < -1/3`: the matching bracket is active; the quartic certificate
    have hmax : max (-(1 + 3 * s) / 2) 0 = -(1 + 3 * s) / 2 := max_eq_left (by linarith)
    rw [hmax]
    have hX : (0:ℝ) ≤ -(1 + 3 * s) / 2 := by linarith
    have hF : F s ≤ 0.8488 * s * (1 + s ^ 2 / 8) := F_le_neg s h1 (by linarith)
    have hmono : 0 ≤ (0.8488 * s * (1 + s ^ 2 / 8) - F s) *
        ((1 - 0.28086 ^ 2) + 0.28086 * (1 + 0.28086) * (-(1 + 3 * s) / 2)) := by
      apply mul_nonneg (by linarith)
      nlinarith [hX]
    have hkey : (0:ℝ) < 0.861 * (1 - (0.8488 * s * (1 + s ^ 2 / 8)) * (1 - 0.28086 ^ 2) +
          (14 / 15) * 0.28086 * (1 - (0.8488 * s * (1 + s ^ 2 / 8)) * (1 + 0.28086)) * (-(1 + 3 * s) / 2)) +
        (1 - 0.861) * (1 + 3 * (14 / 15) * (-(1 + 3 * s) / 2)) - 0.611 * (1 - 3 * s) := by
      rcases le_or_gt s (-1 / 2) with hc | hc
      · have hu : (0:ℝ) ≤ s + 1 := by linarith
        have hv : (0:ℝ) ≤ -1 / 2 - s := by linarith
        have e : 0.861 * (1 - (0.8488 * s * (1 + s ^ 2 / 8)) * (1 - 0.28086 ^ 2) +
              (14 / 15) * 0.28086 * (1 - (0.8488 * s * (1 + s ^ 2 / 8)) * (1 + 0.28086)) * (-(1 + 3 * s) / 2)) +
            (1 - 0.861) * (1 + 3 * (14 / 15) * (-(1 + 3 * s) / 2)) - 0.611 * (1 - 3 * s)
            = 1 / 2000 + (25470552793147013 / 7812500000000000 : ℝ) * (-1 / 2 - s) ^ 4
              + (431844060071557 / 62500000000000 : ℝ) * (s + 1) * (-1 / 2 - s) ^ 3
              + (8924462916791637 / 1953125000000000 : ℝ) * (s + 1) ^ 2 * (-1 / 2 - s) ^ 2
              + (29542825048119359 / 31250000000000000 : ℝ) * (s + 1) ^ 3 * (-1 / 2 - s)
              + (8916012152314763 / 125000000000000000 : ℝ) * (s + 1) ^ 4 := by
          ring
        rw [e]
        positivity
      · rcases le_or_gt s (-5 / 12) with hc2 | hc2
        · have hu : (0:ℝ) ≤ s + 1 / 2 := by linarith
          have hv : (0:ℝ) ≤ -5 / 12 - s := by linarith
          have e : 0.861 * (1 - (0.8488 * s * (1 + s ^ 2 / 8)) * (1 - 0.28086 ^ 2) +
                (14 / 15) * 0.28086 * (1 - (0.8488 * s * (1 + s ^ 2 / 8)) * (1 + 0.28086)) * (-(1 + 3 * s) / 2)) +
              (1 - 0.861) * (1 + 3 * (14 / 15) * (-(1 + 3 * s) / 2)) - 0.611 * (1 - 3 * s)
              = 1 / 2000 + (722196984337495803 / 7812500000000000 : ℝ) * (-5 / 12 - s) ^ 4
                + (443735010244133757 / 1953125000000000 : ℝ) * (s + 1 / 2) * (-5 / 12 - s) ^ 3
                + (3198941529359305203 / 15625000000000000 : ℝ) * (s + 1 / 2) ^ 2 * (-5 / 12 - s) ^ 2
                + (373915912121974593 / 3906250000000000 : ℝ) * (s + 1 / 2) ^ 3 * (-5 / 12 - s)
                + (644683384487022651 / 25000000000000000 : ℝ) * (s + 1 / 2) ^ 4 := by
            ring
          rw [e]
          positivity
        · have hu : (0:ℝ) ≤ s + 5 / 12 := by linarith
          have hv : (0:ℝ) ≤ -1 / 3 - s := by linarith
          have e : 0.861 * (1 - (0.8488 * s * (1 + s ^ 2 / 8)) * (1 - 0.28086 ^ 2) +
                (14 / 15) * 0.28086 * (1 - (0.8488 * s * (1 + s ^ 2 / 8)) * (1 + 0.28086)) * (-(1 + 3 * s) / 2)) +
              (1 - 0.861) * (1 + 3 * (14 / 15) * (-(1 + 3 * s) / 2)) - 0.611 * (1 - 3 * s)
              = 1 / 2000 + (644683384487022651 / 25000000000000000 : ℝ) * (-1 / 3 - s) ^ 4
                + (1727753273947214883 / 15625000000000000 : ℝ) * (s + 5 / 12) * (-1 / 3 - s) ^ 3
                + (243450650358578421 / 976562500000000 : ℝ) * (s + 5 / 12) ^ 2 * (-1 / 3 - s) ^ 2
                + (261974371460613957 / 976562500000000 : ℝ) * (s + 5 / 12) ^ 3 * (-1 / 3 - s)
                + (10137028619831949 / 97656250000000 : ℝ) * (s + 5 / 12) ^ 4 := by
            ring
          rw [e]
          positivity
    nlinarith [hkey, hmono]


#print axioms solution
