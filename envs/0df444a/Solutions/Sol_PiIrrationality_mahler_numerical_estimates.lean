-- Prove2me | solution 1 for PiIrrationality.mahler_numerical_estimates
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-02T16:50:13.688033+00:00
-- url     : https://prove2.me/submissions/df1b1333-6505-43ea-9256-1879bc7b776a

import Mathlib

set_option autoImplicit false
set_option exponentiation.threshold 1000000

/-- Base case for the (n+1)^22 estimate: 51^22 < 10^37.57.
Proved by raising both sides to the 100th power, turning the rpow
into a decidable natural-number inequality. -/
theorem mahler_base22 : ((51 : ℝ)) ^ (22 : ℕ) < (10 : ℝ) ^ ((37.57 : ℝ)) := by
  have hnat : (51 : ℕ) ^ 2200 < (10 : ℕ) ^ 3757 := by decide
  have key : ((((51 : ℝ)) ^ (22 : ℕ)) ^ (100 : ℕ))
      < ((((10 : ℝ) ^ ((37.57 : ℝ)))) ^ (100 : ℕ)) := by
    have hL : ((((51 : ℝ)) ^ (22 : ℕ)) ^ (100 : ℕ)) = (51 : ℝ) ^ (2200 : ℕ) := by
      rw [← pow_mul, show (22 : ℕ) * 100 = 2200 from rfl]
    have hR : ((((10 : ℝ) ^ ((37.57 : ℝ)))) ^ (100 : ℕ)) = (10 : ℝ) ^ (3757 : ℕ) := by
      rw [← Real.rpow_natCast ((10 : ℝ) ^ ((37.57 : ℝ))) 100,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (10 : ℝ)),
        show (37.57 : ℝ) * (((100 : ℕ)) : ℝ) = (((3757 : ℕ)) : ℝ) from by norm_num,
        Real.rpow_natCast]
    rw [hL, hR]
    exact_mod_cast hnat
  by_contra hcon
  push Not at hcon
  have hle :=
    pow_le_pow_left₀ (show (0 : ℝ) ≤ (10 : ℝ) ^ ((37.57 : ℝ)) by positivity) hcon 100
  linarith

/-- Per-step ratio for the (n+1)^22 estimate: (52/51)^22 < 10^0.7514.
Via the 10000th power, a decidable natural-number inequality. -/
theorem mahler_ratio22 : ((52 / 51 : ℝ)) ^ (22 : ℕ) < (10 : ℝ) ^ ((0.7514 : ℝ)) := by
  have hnat : (52 : ℝ) ^ (220000 : ℕ)
      < (10 : ℝ) ^ (7514 : ℕ) * (51 : ℝ) ^ (220000 : ℕ) := by
    have h : (52 : ℕ) ^ 220000 < (10 : ℕ) ^ 7514 * (51 : ℕ) ^ 220000 := by decide
    exact_mod_cast h
  have key : ((((52 / 51 : ℝ)) ^ (22 : ℕ)) ^ (10000 : ℕ))
      < ((((10 : ℝ) ^ ((0.7514 : ℝ)))) ^ (10000 : ℕ)) := by
    have hL : ((((52 / 51 : ℝ)) ^ (22 : ℕ)) ^ (10000 : ℕ))
        = (52 : ℝ) ^ (220000 : ℕ) / (51 : ℝ) ^ (220000 : ℕ) := by
      rw [← pow_mul, show (22 : ℕ) * 10000 = 220000 from rfl, div_pow]
    have hR : ((((10 : ℝ) ^ ((0.7514 : ℝ)))) ^ (10000 : ℕ)) = (10 : ℝ) ^ (7514 : ℕ) := by
      rw [← Real.rpow_natCast ((10 : ℝ) ^ ((0.7514 : ℝ))) 10000,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (10 : ℝ)),
        show (0.7514 : ℝ) * (((10000 : ℕ)) : ℝ) = (((7514 : ℕ)) : ℝ) from by norm_num,
        Real.rpow_natCast]
    rw [hL, hR, div_lt_iff₀ (show (0 : ℝ) < (51 : ℝ) ^ (220000 : ℕ) by positivity)]
    exact hnat
  by_contra hcon
  push Not at hcon
  have hle :=
    pow_le_pow_left₀ (show (0 : ℝ) ≤ (10 : ℝ) ^ ((0.7514 : ℝ)) by positivity) hcon 10000
  linarith

/-- The (n+1)^22 < 10^{0.7514n} estimate for all n ≥ 50, by induction:
base case n = 50, step multiplies by the ratio bound. -/
theorem mahler_pow22 : ∀ m : ℕ, 50 ≤ m →
    ((((m : ℝ) + 1) ^ (22 : ℕ) < (10 : ℝ) ^ ((0.7514 : ℝ) * (m : ℝ)))) := by
  have base : ((((50 : ℕ)) : ℝ) + 1) ^ (22 : ℕ)
      < (10 : ℝ) ^ ((0.7514 : ℝ) * ((((50 : ℕ)) : ℝ))) := by
    have e1 : ((((50 : ℕ)) : ℝ) + 1) = (51 : ℝ) := by norm_num
    have e2 : (0.7514 : ℝ) * ((((50 : ℕ)) : ℝ)) = (37.57 : ℝ) := by norm_num
    rw [e1, e2]
    exact mahler_base22
  have step : ∀ k : ℕ, 50 ≤ k →
      ((((k : ℝ) + 1) ^ (22 : ℕ) < (10 : ℝ) ^ ((0.7514 : ℝ) * (k : ℝ))) →
      (((((k + 1 : ℕ)) : ℝ) + 1) ^ (22 : ℕ)
        < (10 : ℝ) ^ ((0.7514 : ℝ) * (((((k + 1 : ℕ)) : ℝ)))))) := by
    intro k hk ih
    have ecast : (((((k + 1 : ℕ)) : ℝ) + 1)) = (k : ℝ) + 2 := by push_cast; ring
    have erhs : (0.7514 : ℝ) * (((((k + 1 : ℕ)) : ℝ)))
        = (0.7514 : ℝ) * (k : ℝ) + 0.7514 := by push_cast; ring
    rw [ecast, erhs]
    have hle : (k : ℝ) + 2 ≤ ((k : ℝ) + 1) * (52 / 51) := by
      have hrw : ((k : ℝ) + 1) * (52 / 51) - ((k : ℝ) + 2) = ((k : ℝ) - 50) / 51 := by
        ring
      have hnn : (0 : ℝ) ≤ ((k : ℝ) - 50) / 51 := by
        apply div_nonneg _ (by norm_num)
        have hkR : (50 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        linarith
      linarith
    have hpow : ((k : ℝ) + 2) ^ (22 : ℕ) ≤ (((k : ℝ) + 1) * (52 / 51)) ^ (22 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hle 22
    rw [mul_pow] at hpow
    have hmul : ((k : ℝ) + 1) ^ (22 : ℕ) * (52 / 51) ^ (22 : ℕ)
        < (10 : ℝ) ^ ((0.7514 : ℝ) * (k : ℝ)) * (10 : ℝ) ^ ((0.7514 : ℝ)) := by
      have p1 := mul_lt_mul_of_pos_right ih
        (show (0 : ℝ) < (52 / 51) ^ (22 : ℕ) by positivity)
      have p2 := mul_lt_mul_of_pos_left mahler_ratio22
        (show (0 : ℝ) < (10 : ℝ) ^ ((0.7514 : ℝ) * (k : ℝ)) by positivity)
      exact lt_trans p1 p2
    have hexp : (10 : ℝ) ^ ((0.7514 : ℝ) * (k : ℝ)) * (10 : ℝ) ^ ((0.7514 : ℝ))
        = (10 : ℝ) ^ ((0.7514 : ℝ) * (k : ℝ) + 0.7514) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < (10 : ℝ))]
    calc ((k : ℝ) + 2) ^ (22 : ℕ)
        ≤ ((k : ℝ) + 1) ^ (22 : ℕ) * (52 / 51) ^ (22 : ℕ) := hpow
      _ < (10 : ℝ) ^ ((0.7514 : ℝ) * (k : ℝ)) * (10 : ℝ) ^ ((0.7514 : ℝ)) := hmul
      _ = (10 : ℝ) ^ ((0.7514 : ℝ) * (k : ℝ) + 0.7514) := hexp
  intro m hm
  exact Nat.le_induction (m := 50)
    (P := fun n _ => ((((n : ℝ) + 1) ^ (22 : ℕ)
      < (10 : ℝ) ^ ((0.7514 : ℝ) * (n : ℝ)))))
    base step m hm

/-- Base case for the n^11 estimate: 50^11 < 10^18.69, via 100th powers. -/
theorem mahler_base11 : ((50 : ℝ)) ^ (11 : ℕ) < (10 : ℝ) ^ ((18.69 : ℝ)) := by
  have hnat : (50 : ℕ) ^ 1100 < (10 : ℕ) ^ 1869 := by decide
  have key : ((((50 : ℝ)) ^ (11 : ℕ)) ^ (100 : ℕ))
      < ((((10 : ℝ) ^ ((18.69 : ℝ)))) ^ (100 : ℕ)) := by
    have hL : ((((50 : ℝ)) ^ (11 : ℕ)) ^ (100 : ℕ)) = (50 : ℝ) ^ (1100 : ℕ) := by
      rw [← pow_mul, show (11 : ℕ) * 100 = 1100 from rfl]
    have hR : ((((10 : ℝ) ^ ((18.69 : ℝ)))) ^ (100 : ℕ)) = (10 : ℝ) ^ (1869 : ℕ) := by
      rw [← Real.rpow_natCast ((10 : ℝ) ^ ((18.69 : ℝ))) 100,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (10 : ℝ)),
        show (18.69 : ℝ) * (((100 : ℕ)) : ℝ) = (((1869 : ℕ)) : ℝ) from by norm_num,
        Real.rpow_natCast]
    rw [hL, hR]
    exact_mod_cast hnat
  by_contra hcon
  push Not at hcon
  have hle :=
    pow_le_pow_left₀ (show (0 : ℝ) ≤ (10 : ℝ) ^ ((18.69 : ℝ)) by positivity) hcon 100
  linarith

/-- Per-step ratio for the n^11 estimate: (51/50)^11 < 10^0.1869. -/
theorem mahler_ratio11 : ((51 / 50 : ℝ)) ^ (11 : ℕ) < (10 : ℝ) ^ ((0.1869 : ℝ)) := by
  have hnat : (51 : ℝ) ^ (110000 : ℕ)
      < (10 : ℝ) ^ (1869 : ℕ) * (50 : ℝ) ^ (110000 : ℕ) := by
    have h : (51 : ℕ) ^ 110000 < (10 : ℕ) ^ 1869 * (50 : ℕ) ^ 110000 := by decide
    exact_mod_cast h
  have key : ((((51 / 50 : ℝ)) ^ (11 : ℕ)) ^ (10000 : ℕ))
      < ((((10 : ℝ) ^ ((0.1869 : ℝ)))) ^ (10000 : ℕ)) := by
    have hL : ((((51 / 50 : ℝ)) ^ (11 : ℕ)) ^ (10000 : ℕ))
        = (51 : ℝ) ^ (110000 : ℕ) / (50 : ℝ) ^ (110000 : ℕ) := by
      rw [← pow_mul, show (11 : ℕ) * 10000 = 110000 from rfl, div_pow]
    have hR : ((((10 : ℝ) ^ ((0.1869 : ℝ)))) ^ (10000 : ℕ)) = (10 : ℝ) ^ (1869 : ℕ) := by
      rw [← Real.rpow_natCast ((10 : ℝ) ^ ((0.1869 : ℝ))) 10000,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (10 : ℝ)),
        show (0.1869 : ℝ) * (((10000 : ℕ)) : ℝ) = (((1869 : ℕ)) : ℝ) from by norm_num,
        Real.rpow_natCast]
    rw [hL, hR, div_lt_iff₀ (show (0 : ℝ) < (50 : ℝ) ^ (110000 : ℕ) by positivity)]
    exact hnat
  by_contra hcon
  push Not at hcon
  have hle :=
    pow_le_pow_left₀ (show (0 : ℝ) ≤ (10 : ℝ) ^ ((0.1869 : ℝ)) by positivity) hcon 10000
  linarith

/-- The n^11 < 10^{0.3738n} estimate for all n ≥ 50, by induction. -/
theorem mahler_pow11 : ∀ m : ℕ, 50 ≤ m →
    ((((m : ℝ) ^ (11 : ℕ) < (10 : ℝ) ^ ((0.3738 : ℝ) * (m : ℝ))))) := by
  have base : ((((50 : ℕ)) : ℝ)) ^ (11 : ℕ)
      < (10 : ℝ) ^ ((0.3738 : ℝ) * ((((50 : ℕ)) : ℝ))) := by
    have e2 : (0.3738 : ℝ) * ((((50 : ℕ)) : ℝ)) = (18.69 : ℝ) := by norm_num
    rw [e2]
    exact mahler_base11
  have step : ∀ k : ℕ, 50 ≤ k →
      ((((k : ℝ)) ^ (11 : ℕ) < (10 : ℝ) ^ ((0.3738 : ℝ) * (k : ℝ))) →
      (((((k + 1 : ℕ)) : ℝ)) ^ (11 : ℕ)
        < (10 : ℝ) ^ ((0.3738 : ℝ) * (((((k + 1 : ℕ)) : ℝ)))))) := by
    intro k hk ih
    have ecast : (((((k + 1 : ℕ)) : ℝ))) = (k : ℝ) + 1 := by push_cast; ring
    have erhs : (0.3738 : ℝ) * ((k : ℝ) + 1)
        = (0.3738 : ℝ) * (k : ℝ) + 0.3738 := by ring
    rw [ecast, erhs]
    have hle : (k : ℝ) + 1 ≤ (k : ℝ) * (51 / 50) := by
      have hrw : (k : ℝ) * (51 / 50) - ((k : ℝ) + 1) = ((k : ℝ) - 50) / 50 := by ring
      have hnn : (0 : ℝ) ≤ ((k : ℝ) - 50) / 50 := by
        apply div_nonneg _ (by norm_num)
        have hkR : (50 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        linarith
      linarith
    have hpow : ((k : ℝ) + 1) ^ (11 : ℕ) ≤ ((k : ℝ) * (51 / 50)) ^ (11 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hle 11
    rw [mul_pow] at hpow
    have hmul : (k : ℝ) ^ (11 : ℕ) * (51 / 50) ^ (11 : ℕ)
        < (10 : ℝ) ^ ((0.3738 : ℝ) * (k : ℝ)) * (10 : ℝ) ^ ((0.1869 : ℝ)) := by
      have p1 := mul_lt_mul_of_pos_right ih
        (show (0 : ℝ) < (51 / 50) ^ (11 : ℕ) by positivity)
      have p2 := mul_lt_mul_of_pos_left mahler_ratio11
        (show (0 : ℝ) < (10 : ℝ) ^ ((0.3738 : ℝ) * (k : ℝ)) by positivity)
      exact lt_trans p1 p2
    have hexp : (10 : ℝ) ^ ((0.3738 : ℝ) * (k : ℝ)) * (10 : ℝ) ^ ((0.1869 : ℝ))
        = (10 : ℝ) ^ ((0.3738 : ℝ) * (k : ℝ) + 0.1869) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < (10 : ℝ))]
    have hexp2 : (10 : ℝ) ^ ((0.3738 : ℝ) * (k : ℝ) + 0.1869)
        < (10 : ℝ) ^ ((0.3738 : ℝ) * (k : ℝ) + 0.3738) := by
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 10)
      norm_num
    calc ((k : ℝ) + 1) ^ (11 : ℕ)
        ≤ (k : ℝ) ^ (11 : ℕ) * (51 / 50) ^ (11 : ℕ) := hpow
      _ < (10 : ℝ) ^ ((0.3738 : ℝ) * (k : ℝ)) * (10 : ℝ) ^ ((0.1869 : ℝ)) := hmul
      _ = (10 : ℝ) ^ ((0.3738 : ℝ) * (k : ℝ) + 0.1869) := hexp
      _ < (10 : ℝ) ^ ((0.3738 : ℝ) * (k : ℝ) + 0.3738) := hexp2
  intro m hm
  exact Nat.le_induction (m := 50)
    (P := fun n _ => ((((n : ℝ)) ^ (11 : ℕ)
      < (10 : ℝ) ^ ((0.3738 : ℝ) * (n : ℝ)))))
    base step m hm

/-- Transfer from the ℕ-power to the rpow form: n^{11/2} < 10^{0.1869n}. -/
theorem mahler_rpow11 : ∀ m : ℕ, 50 ≤ m →
    ((((m : ℝ) ^ ((11 / 2 : ℝ)) < (10 : ℝ) ^ ((0.1869 : ℝ) * (m : ℝ))))) := by
  intro m hm
  have h11 := mahler_pow11 m hm
  have h11r : ((m : ℝ) ^ ((((11 : ℕ)) : ℝ))) < (10 : ℝ) ^ ((0.3738 : ℝ) * (m : ℝ)) := by
    rw [Real.rpow_natCast]; exact h11
  have e1 : ((11 / 2 : ℝ)) = ((((11 : ℕ)) : ℝ)) * (1 / 2) := by norm_num
  have hposm : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have e2 : (m : ℝ) ^ ((11 / 2 : ℝ)) = ((m : ℝ) ^ ((11:ℕ):ℝ)) ^ ((1 / 2 : ℝ)) := by
    rw [e1, ← Real.rpow_mul hposm]
  rw [e2]
  have hlt := Real.rpow_lt_rpow
    (show (0 : ℝ) ≤ ((m : ℝ) ^ ((((11 : ℕ)) : ℝ))) by
      rw [Real.rpow_natCast]; positivity)
    h11r (show (0 : ℝ) < (1 / 2 : ℝ) by norm_num)
  have e3 : (((10 : ℝ) ^ ((0.3738 : ℝ) * (m : ℝ))) ^ ((1 / 2 : ℝ)))
      = (10 : ℝ) ^ ((0.1869 : ℝ) * (m : ℝ)) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (10 : ℝ))]
    congr 1
    push_cast
    ring
  rwa [e3] at hlt

/-- The 2^{2.6n} ≤ 10^{0.8n} estimate, via 2^26 < 10^8. -/
theorem mahler_2pow : ∀ m : ℕ, 50 ≤ m →
    ((((2 : ℝ) ^ ((2.6 : ℝ) * (m : ℝ)) ≤ (10 : ℝ) ^ ((0.8 : ℝ) * (m : ℝ))))) := by
  intro m hm
  have h26 : (2 : ℝ) ^ ((((26 : ℕ)) : ℝ)) ≤ (10 : ℝ) ^ ((((8 : ℕ)) : ℝ)) := by
    have h : (2 : ℕ) ^ (26 : ℕ) ≤ (10 : ℕ) ^ (8 : ℕ) := by decide
    have hr : (2:ℝ)^(26:ℕ) ≤ (10:ℝ)^(8:ℕ) := by exact_mod_cast h
    rwa [← Real.rpow_natCast (2:ℝ) 26, ← Real.rpow_natCast (10:ℝ) 8] at hr
  have e1 : (2.6 : ℝ) * (m : ℝ) = ((((26 : ℕ)) : ℝ)) * ((m : ℝ) / 10) := by
    ring
  have e2 : (0.8 : ℝ) * (m : ℝ) = ((((8 : ℕ)) : ℝ)) * ((m : ℝ) / 10) := by
    ring
  rw [e1, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (2 : ℝ)),
    e2, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (10 : ℝ))]
  exact Real.rpow_le_rpow (by positivity) h26 (by positivity)

/-- Main theorem: Mahler (1953) §4 numerical estimates. -/
theorem solution (n q : ℕ) (hn : 50 ≤ n) :
    ((n : ℝ) + 1) ^ (22 : ℕ) < (10 : ℝ) ^ ((0.7514 : ℝ) * n)
    ∧ (n : ℝ) ^ ((11 / 2 : ℝ)) < (10 : ℝ) ^ ((0.1869 : ℝ) * n)
    ∧ ((10 : ℝ) ^ ((3.4181 : ℝ) * n) > (10 : ℝ) ^ ((0.4936 : ℝ) * n) * (q : ℝ) ^ (10 : ℕ) →
        (10 : ℝ) ^ ((2.9245 : ℝ) * n) > (q : ℝ) ^ (10 : ℕ))
    ∧ (10 : ℝ) * (Nat.factorial 10 : ℝ) * (2 : ℝ) ^ (30 : ℕ)
        * (((n : ℝ) + 1) ^ (22 : ℕ)) * (2 : ℝ) ^ ((2.6 : ℝ) * n)
        < (10 : ℝ) ^ ((8.9101 : ℝ) * n) := by
  refine ⟨mahler_pow22 n hn, mahler_rpow11 n hn, ?_, ?_⟩
  · intro h
    have hpos : (0 : ℝ) < (10 : ℝ) ^ ((0.4936 : ℝ) * (n : ℝ)) := by positivity
    have hdiv : (q : ℝ) ^ (10 : ℕ)
        < (10 : ℝ) ^ ((3.4181 : ℝ) * (n : ℝ)) / (10 : ℝ) ^ ((0.4936 : ℝ) * (n : ℝ)) := by
      rw [lt_div_iff₀ hpos, mul_comm ((q : ℝ) ^ (10 : ℕ))]
      exact h
    have hexp : (10 : ℝ) ^ ((3.4181 : ℝ) * (n : ℝ)) / (10 : ℝ) ^ ((0.4936 : ℝ) * (n : ℝ))
        = (10 : ℝ) ^ ((2.9245 : ℝ) * (n : ℝ)) := by
      rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < (10 : ℝ))]
      congr 1
      ring
    rwa [hexp] at hdiv
  · have h1 := mahler_pow22 n hn
    have h2 := mahler_2pow n hn
    have hC : (10 : ℝ) * (Nat.factorial 10 : ℝ) * (2 : ℝ) ^ (30 : ℕ)
        = ((((38963943309312000 : ℕ)) : ℝ)) := by
      rw [show Nat.factorial 10 = 3628800 from rfl]
      norm_num
    have hCpos : (0 : ℝ) < ((((38963943309312000 : ℕ)) : ℝ)) := by positivity
    have a1 : (((n : ℝ) + 1) ^ (22 : ℕ)) * (2 : ℝ) ^ ((2.6 : ℝ) * (n : ℝ))
        < (10 : ℝ) ^ ((0.7514 : ℝ) * (n : ℝ)) * (10 : ℝ) ^ ((0.8 : ℝ) * (n : ℝ)) := by
      have p1 : (((n : ℝ) + 1) ^ (22 : ℕ)) * (2 : ℝ) ^ ((2.6 : ℝ) * (n : ℝ))
          < (10 : ℝ) ^ ((0.7514 : ℝ) * (n : ℝ)) * (2 : ℝ) ^ ((2.6 : ℝ) * (n : ℝ)) :=
        mul_lt_mul_of_pos_right h1 (by positivity)
      have p2 : (10 : ℝ) ^ ((0.7514 : ℝ) * (n : ℝ)) * (2 : ℝ) ^ ((2.6 : ℝ) * (n : ℝ))
          ≤ (10 : ℝ) ^ ((0.7514 : ℝ) * (n : ℝ)) * (10 : ℝ) ^ ((0.8 : ℝ) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      exact lt_of_lt_of_le p1 p2
    have step1 : (10 : ℝ) * (Nat.factorial 10 : ℝ) * (2 : ℝ) ^ (30 : ℕ)
          * (((n : ℝ) + 1) ^ (22 : ℕ)) * (2 : ℝ) ^ ((2.6 : ℝ) * (n : ℝ))
        < ((((38963943309312000 : ℕ)) : ℝ))
          * (10 : ℝ) ^ ((0.7514 : ℝ) * (n : ℝ)) * (10 : ℝ) ^ ((0.8 : ℝ) * (n : ℝ)) := by
      rw [hC]
      have key2 := mul_lt_mul_of_pos_left a1 hCpos
      simp only [mul_assoc] at key2 ⊢
      exact key2
    have step2 : ((((38963943309312000 : ℕ)) : ℝ))
          * (10 : ℝ) ^ ((0.7514 : ℝ) * (n : ℝ)) * (10 : ℝ) ^ ((0.8 : ℝ) * (n : ℝ))
        ≤ (10 : ℝ) ^ ((8.9101 : ℝ) * (n : ℝ)) := by
      have hClt : ((((38963943309312000 : ℕ)) : ℝ)) ≤ (10 : ℝ) ^ (17 : ℕ) := by
        have h : (38963943309312000 : ℕ) ≤ (10 : ℕ) ^ (17 : ℕ) := by decide
        exact_mod_cast h
      have e : (10 : ℝ) ^ (17 : ℕ) * (10 : ℝ) ^ ((0.7514 : ℝ) * (n : ℝ))
            * (10 : ℝ) ^ ((0.8 : ℝ) * (n : ℝ))
          = (10 : ℝ) ^ ((17 : ℝ) + (0.7514 : ℝ) * (n : ℝ) + (0.8 : ℝ) * (n : ℝ)) := by
        rw [← Real.rpow_natCast (10 : ℝ) 17,
          ← Real.rpow_add (by norm_num : (0 : ℝ) < (10 : ℝ)),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < (10 : ℝ))]
        congr 1
      have hexp : (17 : ℝ) + (0.7514 : ℝ) * (n : ℝ) + (0.8 : ℝ) * (n : ℝ)
          ≤ (8.9101 : ℝ) * (n : ℝ) := by
        have hnR : (50 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      calc ((((38963943309312000 : ℕ)) : ℝ))
              * (10 : ℝ) ^ ((0.7514 : ℝ) * (n : ℝ)) * (10 : ℝ) ^ ((0.8 : ℝ) * (n : ℝ))
          ≤ (10 : ℝ) ^ (17 : ℕ) * (10 : ℝ) ^ ((0.7514 : ℝ) * (n : ℝ))
              * (10 : ℝ) ^ ((0.8 : ℝ) * (n : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact hClt
        _ = (10 : ℝ) ^ ((17 : ℝ) + (0.7514 : ℝ) * (n : ℝ)
              + (0.8 : ℝ) * (n : ℝ)) := e
        _ ≤ (10 : ℝ) ^ ((8.9101 : ℝ) * (n : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 10) hexp
    exact lt_of_lt_of_le step1 step2

/-- Dual-named alias for the published node (ascribed, per the pipeline recipe). -/
theorem PiIrrationality.mahler_numerical_estimates (n q : ℕ) (hn : 50 ≤ n) :
    ((n : ℝ) + 1) ^ (22 : ℕ) < (10 : ℝ) ^ ((0.7514 : ℝ) * n)
    ∧ (n : ℝ) ^ ((11 / 2 : ℝ)) < (10 : ℝ) ^ ((0.1869 : ℝ) * n)
    ∧ ((10 : ℝ) ^ ((3.4181 : ℝ) * n) > (10 : ℝ) ^ ((0.4936 : ℝ) * n) * (q : ℝ) ^ (10 : ℕ) →
        (10 : ℝ) ^ ((2.9245 : ℝ) * n) > (q : ℝ) ^ (10 : ℕ))
    ∧ (10 : ℝ) * (Nat.factorial 10 : ℝ) * (2 : ℝ) ^ (30 : ℕ)
        * (((n : ℝ) + 1) ^ (22 : ℕ)) * (2 : ℝ) ^ ((2.6 : ℝ) * n)
        < (10 : ℝ) ^ ((8.9101 : ℝ) * n) :=
  solution n q hn
