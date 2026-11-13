-- Prove2me | solution 1 for StaticCalendar.limit_term_increasing
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-12T13:38:12.2243+00:00
-- url     : https://prove2.me/submissions/226410eb-e920-470d-9482-918ff9262d78

import Mathlib

set_option autoImplicit false

/-- The limit term `1 - b^b e^{-b}/b!` is strictly increasing for `b ≥ 1`, since consecutive
ratios are `(1 + 1/b)^b / e < 1`. -/
theorem solution :
    StrictMonoOn (fun b : ℕ => 1 - (b : ℝ) ^ b * Real.exp (-(b : ℝ)) / (b.factorial : ℝ))
      (Set.Ici 1) ∧
    (1 : ℝ) - ((1 : ℕ) : ℝ) ^ 1 * Real.exp (-((1 : ℕ) : ℝ)) / ((1 : ℕ).factorial : ℝ) =
      1 - Real.exp (-1) := by
  constructor
  · let g : ℕ → ℝ := fun n => (n : ℝ) ^ n * Real.exp (-(n : ℝ)) / (n.factorial : ℝ)
    have hstep : ∀ b : ℕ, 1 ≤ b → g (b + 1) < g b := by
      intro b hb
      have hbpos_nat : 0 < b := by omega
      have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbpos_nat
      have hbne : (b : ℝ) ≠ 0 := hbpos.ne'
      have hbase : 0 < 1 + 1 / (b : ℝ) := by positivity
      have hfact_pos : (0 : ℝ) < (b.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos b
      have hg_pos : 0 < g b := by
        dsimp only [g]
        exact div_pos (mul_pos (pow_pos hbpos b) (Real.exp_pos _)) hfact_pos
      have hlog : Real.log (1 + 1 / (b : ℝ)) < 1 / (b : ℝ) := by
        have hx2 : 1 + 1 / (b : ℝ) ≠ 1 := by
          have hpos : (0 : ℝ) < 1 / (b : ℝ) := by positivity
          linarith
        have h := Real.log_lt_sub_one_of_pos hbase hx2
        simpa using h
      have hlogb : (b : ℝ) * Real.log (1 + 1 / (b : ℝ)) < 1 := by
        calc (b : ℝ) * Real.log (1 + 1 / (b : ℝ)) < (b : ℝ) * (1 / (b : ℝ)) :=
              mul_lt_mul_of_pos_left hlog hbpos
          _ = 1 := by field_simp
      have hpoweq : (1 + 1 / (b : ℝ)) ^ b =
          Real.exp ((b : ℝ) * Real.log (1 + 1 / (b : ℝ))) := by
        rw [← Real.exp_log (pow_pos hbase b), Real.log_pow]
      have hratio_lt : (1 + 1 / (b : ℝ)) ^ b / Real.exp 1 < 1 := by
        rw [div_lt_one (Real.exp_pos 1), hpoweq]
        exact Real.exp_lt_exp.mpr hlogb
      have hratio_eq : g (b + 1) = ((1 + 1 / (b : ℝ)) ^ b / Real.exp 1) * g b := by
        dsimp only [g]
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        rw [show -((b : ℝ) + 1) = -(b : ℝ) + (-1) by ring, Real.exp_add, Real.exp_neg]
        rw [show (1 + 1 / (b : ℝ)) = ((b : ℝ) + 1) / (b : ℝ) by field_simp]
        rw [div_pow, pow_succ]
        have hb1 : ((b : ℝ) + 1) ≠ 0 := by positivity
        have hbfact : (b.factorial : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b)
        field_simp [hbne, hb1, hbfact, (Real.exp_pos 1).ne', (Real.exp_pos (-(b : ℝ))).ne']
        rw [← Real.exp_add]
        norm_num
      calc g (b + 1) = ((1 + 1 / (b : ℝ)) ^ b / Real.exp 1) * g b := hratio_eq
        _ < 1 * g b := mul_lt_mul_of_pos_right hratio_lt hg_pos
        _ = g b := one_mul _
    apply strictMonoOn_Ici_of_pred_lt
    intro m hm
    have hb : 1 ≤ m - 1 := by omega
    have hm_eq : m = (m - 1) + 1 := by omega
    rw [Order.pred_eq_sub_one, hm_eq]
    change 1 - g (m - 1) < 1 - g ((m - 1) + 1)
    exact sub_lt_sub_left (hstep (m - 1) hb) 1
  · norm_num
