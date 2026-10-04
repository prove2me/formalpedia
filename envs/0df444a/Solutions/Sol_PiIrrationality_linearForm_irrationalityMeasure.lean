-- Prove2me | solution 1 for PiIrrationality.linearForm_irrationalityMeasure
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T01:50:07.47066+00:00
-- url     : https://prove2.me/submissions/c80c6132-61a9-416b-9373-62b49655d5d6

import Definitions.Def_PiIrrationality_UpperBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Filter Real PiIrrationality

lemma rateExponent_le (C0 C1 δ η : ℝ) (hC0 : 0 < C0) (hC1 : 0 < C1) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hηdef : η = δ * C0 ^ 2 / (2 * (3 * C0 + C1 + 1))) :
    0 < η ∧ η < C0 ∧ (C0 + C1 + 2 * η) / (C0 - η) ≤ 1 + C1 / C0 + δ := by
  have hden : 0 < 2 * (3 * C0 + C1 + 1) := by positivity
  have hη : 0 < η := by rw [hηdef]; positivity
  have hηC0 : η * (2 * (3 * C0 + C1 + 1)) = δ * C0 ^ 2 := by
    rw [hηdef]; field_simp
  have hlt : η < C0 := by
    have : η * (2 * (3 * C0 + C1 + 1)) < C0 * (2 * (3 * C0 + C1 + 1)) := by
      rw [hηC0]
      nlinarith [hC0, hC1, hδ, hδ1]
    exact (mul_lt_mul_iff_of_pos_right hden).mp this
  have hsub : 0 < C0 - η := sub_pos.mpr hlt
  refine ⟨hη, hlt, ?_⟩
  rw [div_le_iff₀ hsub]
  have htarget :
      (C0 + C1 + 2 * η) * C0 ≤ (C0 + C1 + δ * C0) * (C0 - η) := by
    have hdiff :
        (C0 + C1 + δ * C0) * (C0 - η) - (C0 + C1 + 2 * η) * C0 =
          δ * C0 ^ 2 * ((3 - δ) * C0 + C1 + 2) / (2 * (3 * C0 + C1 + 1)) := by
      rw [hηdef]
      field_simp [hden.ne']
      ring
    have hnum : 0 ≤ δ * C0 ^ 2 * ((3 - δ) * C0 + C1 + 2) := by
      have hbracket : 0 ≤ (3 - δ) * C0 + C1 + 2 := by nlinarith [hC0, hC1, hδ1]
      positivity
    have hquot : 0 ≤ δ * C0 ^ 2 * ((3 - δ) * C0 + C1 + 2) / (2 * (3 * C0 + C1 + 1)) :=
      div_nonneg hnum hden.le
    linarith [hdiff, hquot]
  apply (mul_le_mul_iff_of_pos_right hC0).mp
  calc
    (C0 + C1 + 2 * η) * C0 ≤ (C0 + C1 + δ * C0) * (C0 - η) := htarget
    _ = (1 + C1 / C0 + δ) * (C0 - η) * C0 := by field_simp


theorem solution
    (a b : ℕ → ℤ) (C0 C1 B : ℝ)
    (hC0 : 0 < C0) (hC1 : 0 < C1)
    (hB : 1 + C1 / C0 ≤ B)
    (hb : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      b n ≠ 0 ∧ Real.log |(b n : ℝ)| ≤ (C1 + ε) * n)
    (hΛ : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      0 < |(b n : ℝ) * Real.pi - (a n : ℝ)| ∧
        |Real.log |(b n : ℝ) * Real.pi - (a n : ℝ)| / (n : ℝ) + C0| ≤ ε) :
    UpperBound B := by
  intro ε hε
  let ε' : ℝ := min ε 1
  have hε' : 0 < ε' := lt_min hε zero_lt_one
  have hε'le : ε' ≤ ε := min_le_left _ _
  let δ : ℝ := ε' / 2
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    have hε1 : ε' ≤ 1 := min_le_right _ _
    dsimp [δ]
    linarith
  let η : ℝ := δ * C0 ^ 2 / (2 * (3 * C0 + C1 + 1))
  obtain ⟨hη, hηlt, hEle⟩ := rateExponent_le C0 C1 δ η hC0 hC1 hδ hδ1 rfl
  have hC0η : 0 < C0 - η := sub_pos.mpr hηlt
  let E : ℝ := (C0 + C1 + 2 * η) / (C0 - η)
  have hEB : E ≤ B + δ := by linarith [hB, hEle]
  have hEpos : 0 ≤ E := by positivity
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (hb η hη)
  obtain ⟨N2, hN2⟩ := eventually_atTop.mp (hΛ η hη)
  let N : ℕ := max (max N1 N2) 1
  let φ : ℝ := (C1 + η) / (C0 - η)
  have hφE : 1 + φ ≤ E := by
    have hφ : φ ≤ (C1 + 3 * η) / (C0 - η) := by
      rw [div_le_div_iff_of_pos_right hC0η]
      linarith
    have : 1 + (C1 + 3 * η) / (C0 - η) = E := by
      simp only [E]
      field_simp [hC0η.ne']
      ring
    linarith
  let c0 : ℝ := Real.exp (-(C0 + C1 + 2 * η) * ((N : ℝ) + 1)) / (2 : ℝ) ^ E
  let c1 : ℝ := 1 / (2 * Real.exp ((C1 + η) * ((N : ℝ) + 1)) * (2 : ℝ) ^ φ)
  let c : ℝ := min c0 c1
  have hc : 0 < c := by
    have hc0 : 0 < c0 := by positivity
    have hc1 : 0 < c1 := by positivity
    exact lt_min hc0 hc1
  let Q : ℕ := max 2 (Nat.ceil (((1 / c) : ℝ) ^ (1 / δ)) + 1)
  refine ⟨Q, ?_⟩
  intro p q hq hQle
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.succ_le_of_lt hq
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast le_trans (le_max_left 2 _) hQle
  have htwoq : 0 < 2 * (q : ℝ) := by positivity
  let x : ℝ := Real.log (2 * (q : ℝ)) / (C0 - η)
  have hx0 : 0 ≤ x := div_nonneg (Real.log_nonneg (by linarith)) hC0η.le
  let n : ℕ := max N (Nat.ceil x)
  have hnN : N ≤ n := le_max_left _ _
  have hnx : x ≤ (n : ℝ) := by
    exact (Nat.le_ceil x).trans (by exact_mod_cast le_max_right N (Nat.ceil x))
  have hn1 : 1 ≤ n := le_trans (le_max_right (max N1 N2) 1) hnN
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.one_pos hn1)
  have hnup : (n : ℝ) ≤ x + (N : ℝ) + 1 := by
    by_cases hceil : N ≤ Nat.ceil x
    · rw [show n = Nat.ceil x from max_eq_right hceil]
      have : ((Nat.ceil x : ℕ) : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
      have : (0 : ℝ) ≤ N := by positivity
      linarith
    · rw [show n = N from max_eq_left (le_of_not_ge hceil)]
      linarith [hx0]
  have hbn := hN1 n (le_trans (le_trans (le_max_left N1 N2) (le_max_left _ 1)) hnN)
  have hLn := hN2 n (le_trans (le_trans (le_max_right N1 N2) (le_max_left _ 1)) hnN)
  let Λ : ℝ := (b n : ℝ) * π - (a n : ℝ)
  have hΛpos : 0 < |Λ| := hLn.1
  have habs : |Real.log |Λ| / (n : ℝ) + C0| ≤ η := hLn.2
  have hlog_hi : Real.log |Λ| ≤ -((C0 - η) * (n : ℝ)) := by
    have hdiv : Real.log |Λ| / (n : ℝ) ≤ -(C0 - η) := by linarith [abs_le.mp habs]
    linarith [(div_le_iff₀ hnpos).mp hdiv]
  have hlog_lo : -((C0 + η) * (n : ℝ)) ≤ Real.log |Λ| := by
    have hdiv : -(C0 + η) ≤ Real.log |Λ| / (n : ℝ) := by linarith [abs_le.mp habs]
    linarith [(le_div_iff₀ hnpos).mp hdiv]
  have hΛ_le : |Λ| ≤ Real.exp (-((C0 - η) * (n : ℝ))) := by
    rw [← exp_log hΛpos]; exact exp_le_exp.mpr hlog_hi
  have hΛ_ge : Real.exp (-((C0 + η) * (n : ℝ))) ≤ |Λ| := by
    rw [← exp_log hΛpos]; exact exp_le_exp.mpr hlog_lo
  have hbne : b n ≠ 0 := hbn.1
  have hbpos : (0 : ℝ) < |(b n : ℝ)| := by
    have : (1 : ℤ) ≤ |b n| := Int.one_le_abs hbne
    exact_mod_cast (lt_of_lt_of_le Int.zero_lt_one this)
  have hbexp : |(b n : ℝ)| ≤ Real.exp ((C1 + η) * (n : ℝ)) := by
    rw [← exp_log hbpos]
    exact exp_le_exp.mpr hbn.2
  have hxmul : (C0 - η) * x = log (2 * (q : ℝ)) := by
    simp only [x]
    exact mul_div_cancel₀ _ hC0η.ne'
  have hΛsmall : |Λ| ≤ 1 / (2 * (q : ℝ)) := by
    have hrate : log (2 * (q : ℝ)) ≤ (C0 - η) * (n : ℝ) := by
      rw [← hxmul]
      exact mul_le_mul_of_nonneg_left hnx hC0η.le
    have : |Λ| ≤ exp (-log (2 * (q : ℝ))) :=
      le_trans hΛ_le (exp_le_exp.mpr (by linarith))
    rw [exp_neg, exp_log htwoq] at this
    simpa [one_div] using this
  have hcoeff : 0 ≤ C0 + C1 + 2 * η := by positivity
  have hxE : (C0 + C1 + 2 * η) * x = E * log (2 * (q : ℝ)) := by
    simp only [E, x]
    field_simp [hC0η.ne']
  have hexp_form : exp (-(C0 + C1 + 2 * η) * (x + (N : ℝ) + 1)) =
      exp (-(C0 + C1 + 2 * η) * ((N : ℝ) + 1)) * (2 * (q : ℝ)) ^ (-E) := by
    have hsplit : (-(C0 + C1 + 2 * η)) * (x + (N : ℝ) + 1) =
        (-(C0 + C1 + 2 * η)) * ((N : ℝ) + 1) + (-(C0 + C1 + 2 * η)) * x := by ring
    have hxneg : (-(C0 + C1 + 2 * η)) * x = log (2 * (q : ℝ)) * (-E) := by
      rw [neg_mul, hxE]
      ring
    rw [hsplit, exp_add, hxneg, ← rpow_def_of_pos htwoq]
  have hexp_n : exp (-(C0 + C1 + 2 * η) * ((N : ℝ) + 1)) * (2 * (q : ℝ)) ^ (-E) ≤
      exp (-(C0 + C1 + 2 * η) * (n : ℝ)) := by
    have hmul : (C0 + C1 + 2 * η) * (n : ℝ) ≤ (C0 + C1 + 2 * η) * (x + (N : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hnup hcoeff
    have hexp := exp_le_exp.mpr (neg_le_neg hmul)
    rw [← neg_mul, ← neg_mul] at hexp
    rwa [hexp_form] at hexp
  have hc0_form : c0 / (q : ℝ) ^ E =
      exp (-(C0 + C1 + 2 * η) * ((N : ℝ) + 1)) * (2 * (q : ℝ)) ^ (-E) := by
    have h2 : (2 * (q : ℝ)) ^ (-E) = (2 : ℝ) ^ (-E) * (q : ℝ) ^ (-E) :=
      mul_rpow (by norm_num) hqpos.le
    simp only [c0]
    rw [h2, rpow_neg (by norm_num : (0 : ℝ) ≤ 2), rpow_neg hqpos.le]
    field_simp
  have hc0_le : c0 / (q : ℝ) ^ E ≤ exp (-(C0 + C1 + 2 * η) * (n : ℝ)) :=
    le_trans (le_of_eq hc0_form) hexp_n
  let M : ℤ := b n * p - (q : ℤ) * a n
  have hMcast : (q : ℝ) * Λ - (b n : ℝ) * ((q : ℝ) * π - (p : ℝ)) = (M : ℝ) := by
    simp only [Λ, M]
    push_cast
    ring
  have hdiff_abs : |(q : ℝ) * π - (p : ℝ)| = (q : ℝ) * |π - (p : ℝ) / q| := by
    have hsub : (q : ℝ) * π - (p : ℝ) = (q : ℝ) * (π - (p : ℝ) / q) := by
      field_simp [hqpos.ne']
    rw [hsub, abs_mul, abs_of_pos hqpos]
  have hlower : c / (q : ℝ) ^ E ≤ |π - (p : ℝ) / q| := by
    by_cases hM : M = 0
    · have hEq : (q : ℝ) * Λ = (b n : ℝ) * ((q : ℝ) * π - (p : ℝ)) := by
        rw [← sub_eq_zero, hMcast]
        simp [hM]
      have habs_eq : (q : ℝ) * |Λ| = |(b n : ℝ)| * |(q : ℝ) * π - (p : ℝ)| := by
        simpa [abs_mul, abs_of_pos hqpos] using congrArg abs hEq
      have hratio : |π - (p : ℝ) / q| = |Λ| / |(b n : ℝ)| := by
        have hmul : (q : ℝ) * |Λ| = (q : ℝ) * (|(b n : ℝ)| * |π - (p : ℝ) / q|) := by
          rw [hdiff_abs] at habs_eq
          simpa [mul_assoc, mul_comm, mul_left_comm] using habs_eq
        have hcancel := mul_left_cancel₀ hqpos.ne' hmul
        rw [eq_div_iff hbpos.ne', hcancel, mul_comm]
      have hquot : exp (-(C0 + C1 + 2 * η) * (n : ℝ)) ≤ |Λ| / |(b n : ℝ)| := by
        rw [le_div_iff₀ hbpos, mul_comm]
        calc
          |(b n : ℝ)| * exp (-(C0 + C1 + 2 * η) * (n : ℝ))
              ≤ exp ((C1 + η) * (n : ℝ)) * exp (-(C0 + C1 + 2 * η) * (n : ℝ)) :=
                mul_le_mul_of_nonneg_right hbexp (exp_pos _).le
          _ = exp (-((C0 + η) * (n : ℝ))) := by
              rw [← exp_add]
              congr 1
              ring
          _ ≤ |Λ| := hΛ_ge
      have hpow : c0 / (q : ℝ) ^ E ≤ |Λ| / |(b n : ℝ)| := le_trans hc0_le hquot
      have hcmin : c / (q : ℝ) ^ E ≤ c0 / (q : ℝ) ^ E :=
        div_le_div_of_nonneg_right (min_le_left _ _) (rpow_nonneg hqpos.le _)
      rw [hratio]
      exact le_trans hcmin hpow
    · have hM1 : (1 : ℝ) ≤ |(M : ℝ)| := by exact_mod_cast Int.one_le_abs hM
      have hqΛ : (q : ℝ) * |Λ| ≤ 1 / 2 := by
        have hmul := mul_le_mul_of_nonneg_left hΛsmall hqpos.le
        have hcanc : (q : ℝ) * (1 / (2 * (q : ℝ))) = 1 / 2 := by field_simp
        linarith
      have htri : |(M : ℝ)| ≤ |(q : ℝ) * Λ| + |(b n : ℝ) * ((q : ℝ) * π - (p : ℝ))| := by
        calc
          |(M : ℝ)| = |(q : ℝ) * Λ - (b n : ℝ) * ((q : ℝ) * π - (p : ℝ))| := by
            rw [hMcast.symm]
          _ = |(q : ℝ) * Λ + -((b n : ℝ) * ((q : ℝ) * π - (p : ℝ)))| := by rw [sub_eq_add_neg]
          _ ≤ |(q : ℝ) * Λ| + |-((b n : ℝ) * ((q : ℝ) * π - (p : ℝ)))| := abs_add_le _ _
          _ = |(q : ℝ) * Λ| + |(b n : ℝ) * ((q : ℝ) * π - (p : ℝ))| := by rw [abs_neg]
      have hhalf : 1 / 2 ≤ |(b n : ℝ)| * |(q : ℝ) * π - (p : ℝ)| := by
        have htri' : |(M : ℝ)| ≤ (q : ℝ) * |Λ| + |(b n : ℝ)| * |(q : ℝ) * π - (p : ℝ)| := by
          simpa [abs_mul, abs_of_pos hqpos] using htri
        linarith
      have hge : 1 / (2 * (q : ℝ) * |(b n : ℝ)|) ≤ |π - (p : ℝ) / q| := by
        rw [hdiff_abs] at hhalf
        have hmul : (1 / 2 : ℝ) ≤ |(b n : ℝ)| * (q : ℝ) * |π - (p : ℝ) / q| := by
          simpa [mul_assoc] using hhalf
        rw [div_le_iff₀ (by positivity : 0 < 2 * (q : ℝ) * |(b n : ℝ)|)]
        linarith
      have hxφ : (C1 + η) * x = φ * log (2 * (q : ℝ)) := by
        simp only [φ, x]
        field_simp [hC0η.ne']
      have hexpφ : exp ((C1 + η) * (x + (N : ℝ) + 1)) =
          exp ((C1 + η) * ((N : ℝ) + 1)) * (2 * (q : ℝ)) ^ φ := by
        have hsplit : (C1 + η) * (x + (N : ℝ) + 1) =
            (C1 + η) * ((N : ℝ) + 1) + (C1 + η) * x := by ring
        rw [hsplit, exp_add, hxφ]
        rw [show φ * log (2 * (q : ℝ)) = log (2 * (q : ℝ)) * φ by ring]
        rw [← rpow_def_of_pos htwoq]
      have hform : c1 / (q : ℝ) ^ (1 + φ) =
          1 / (2 * (q : ℝ) * exp ((C1 + η) * (x + (N : ℝ) + 1))) := by
        have h2 : (2 * (q : ℝ)) ^ φ = (2 : ℝ) ^ φ * (q : ℝ) ^ φ :=
          mul_rpow (by norm_num) hqpos.le
        have hqpow : (q : ℝ) * (q : ℝ) ^ φ = (q : ℝ) ^ (1 + φ) := by
          nth_rw 1 [← rpow_one (q : ℝ)]
          rw [← rpow_add hqpos]
        simp only [c1, hexpφ, h2]
        rw [div_div]
        apply congrArg (fun t => 1 / t)
        rw [← hqpow]
        ring
      have hden1 : 2 * (q : ℝ) * |(b n : ℝ)| ≤ 2 * (q : ℝ) * exp ((C1 + η) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hbexp (by positivity)
      have hrec1 : 1 / (2 * (q : ℝ) * exp ((C1 + η) * (n : ℝ))) ≤
          1 / (2 * (q : ℝ) * |(b n : ℝ)|) :=
        one_div_le_one_div_of_le (by positivity) hden1
      have hnexp : exp ((C1 + η) * (n : ℝ)) ≤ exp ((C1 + η) * (x + (N : ℝ) + 1)) :=
        exp_le_exp.mpr (mul_le_mul_of_nonneg_left hnup (by positivity))
      have hden2 : 2 * (q : ℝ) * exp ((C1 + η) * (n : ℝ)) ≤
          2 * (q : ℝ) * exp ((C1 + η) * (x + (N : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hnexp (by positivity)
      have hrec2 : 1 / (2 * (q : ℝ) * exp ((C1 + η) * (x + (N : ℝ) + 1))) ≤
          1 / (2 * (q : ℝ) * exp ((C1 + η) * (n : ℝ))) :=
        one_div_le_one_div_of_le (by positivity) hden2
      have hc1_le : c1 / (q : ℝ) ^ (1 + φ) ≤ 1 / (2 * (q : ℝ) * |(b n : ℝ)|) := by
        rw [hform]
        exact le_trans hrec2 hrec1
      have hφpow : (q : ℝ) ^ (1 + φ) ≤ (q : ℝ) ^ E := rpow_le_rpow_of_exponent_le hq1 hφE
      have hweaken : c1 / (q : ℝ) ^ E ≤ c1 / (q : ℝ) ^ (1 + φ) :=
        div_le_div_of_nonneg_left (by positivity : 0 ≤ c1) (rpow_pos_of_pos hqpos _) hφpow
      have hcmin : c / (q : ℝ) ^ E ≤ c1 / (q : ℝ) ^ E :=
        div_le_div_of_nonneg_right (min_le_right _ _) (rpow_nonneg hqpos.le _)
      exact le_trans hcmin (le_trans hweaken (le_trans hc1_le hge))
  have hlower_B : c / (q : ℝ) ^ (B + δ) ≤ |π - (p : ℝ) / q| := by
    have hEq : (q : ℝ) ^ E ≤ (q : ℝ) ^ (B + δ) := rpow_le_rpow_of_exponent_le hq1 hEB
    exact le_trans (div_le_div_of_nonneg_left hc.le (rpow_pos_of_pos hqpos _) hEq) hlower
  have hroot_lt : ((1 / c) : ℝ) ^ (1 / δ) < (q : ℝ) := by
    have hle : ((1 / c) : ℝ) ^ (1 / δ) ≤ ((Nat.ceil (((1 / c) : ℝ) ^ (1 / δ)) : ℕ) : ℝ) :=
      Nat.le_ceil _
    have hqge : ((Nat.ceil (((1 / c) : ℝ) ^ (1 / δ)) : ℕ) : ℝ) + 1 ≤ q := by
      exact_mod_cast le_trans (le_max_right 2 _) hQle
    linarith
  have hpowδ : (1 : ℝ) / c < (q : ℝ) ^ δ := by
    have hlt := rpow_lt_rpow (by positivity) hroot_lt hδ
    have hident : (((1 / c) : ℝ) ^ (1 / δ)) ^ δ = 1 / c := by
      rw [← rpow_mul (by positivity : 0 ≤ (1 / c : ℝ))]
      have : (1 / δ) * δ = 1 := by field_simp
      rw [this, rpow_one]
    rw [hident] at hlt
    exact hlt
  have hstrict : 1 / (q : ℝ) ^ (B + ε') < c / (q : ℝ) ^ (B + δ) := by
    have hsplit : (q : ℝ) ^ (B + ε') = (q : ℝ) ^ (B + δ) * (q : ℝ) ^ δ := by
      have hεδ : ε' = δ + δ := by simp only [δ]; ring
      rw [show B + ε' = B + δ + δ by linarith, rpow_add hqpos]
    have hassoc : 1 / ((q : ℝ) ^ (B + δ) * (q : ℝ) ^ δ) =
        (1 / (q : ℝ) ^ δ) / (q : ℝ) ^ (B + δ) := by field_simp
    have hfrac : 1 / (q : ℝ) ^ δ < c := by
      rw [div_lt_iff₀ (rpow_pos_of_pos hqpos δ)]
      have h1 : (1 : ℝ) < (q : ℝ) ^ δ * c := (div_lt_iff₀ hc).mp hpowδ
      rwa [mul_comm] at h1
    rw [hsplit, hassoc]
    exact (div_lt_div_iff_of_pos_right (rpow_pos_of_pos hqpos _)).mpr hfrac
  have hεpow : 1 / (q : ℝ) ^ (B + ε) ≤ 1 / (q : ℝ) ^ (B + ε') := by
    exact one_div_le_one_div_of_le (rpow_pos_of_pos hqpos _)
      (rpow_le_rpow_of_exponent_le hq1 (by linarith : B + ε' ≤ B + ε))
  exact lt_of_le_of_lt hεpow (lt_of_lt_of_le hstrict hlower_B)
