-- Prove2me | solution 1 for Tao2022Collatz.section5_parameter_estimates
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T01:34:24.647216+00:00
-- url     : https://prove2.me/submissions/8465d3d7-f3d0-4999-a3de-af5c6a0a61ee

import Mathlib
import Definitions.Def_weightedLogMassReal
import Definitions.Def_syracuseOrbitMin

set_option autoImplicit false

/-! Tao, Almost all Collatz orbits attain almost bounded values (arXiv:1909.03562v7).
Foundational layer for Theorem 3.1: the n-Syracuse valuation, the affine iterate formula
(Tao (1.5)/(1.7)) and the orbit-minimum facts used in Section 3. -/

namespace Tao31

noncomputable def alph : ℝ := 1001 / 1000

section Num120

/-! Parameters of Tao (5.20) as functions of `x` (log x = u^5). -/
noncomputable def pn0 (x : ℝ) : ℕ := ⌊Real.log x / (10 * Real.log 2)⌋₊
noncomputable def pD (x : ℝ) : ℝ := 2 * Real.log x ^ ((3 : ℝ) / 5)
noncomputable def pL (x : ℝ) : ℝ := Real.log x ^ ((1 : ℝ) / 5)
noncomputable def pW (x : ℝ) : ℝ := 2 * ((2 * pD x + 1) * Real.log 2) + Real.log (4 / 3)
noncomputable def pm0 (x : ℝ) : ℕ :=
  ⌈(pW x + 2 * ((2 * pD x + 1) * Real.log 2) + 1) / Real.log (4 / 3)⌉₊
noncomputable def pWt (x : ℝ) : ℝ := pW x + pD x * Real.log 2 + Real.log 2
noncomputable def pK (x : ℝ) : ℕ := ⌈2 * (pn0 x : ℝ) + pD x⌉₊
noncomputable def pMmax (x : ℝ) : ℕ :=
  ⌊Real.exp (Real.log x + pm0 x * Real.log (4 / 3) + pW x)⌋₊ + 1
noncomputable def peps (x : ℝ) : ℝ := 2 * (3 / 2 : ℝ) ^ (pn0 x) / x
noncomputable def pDm (x : ℝ) : ℕ := ⌈4 * pD x + 2⌉₊

lemma l2_bd : 0.6931 < Real.log 2 ∧ Real.log 2 < 0.6932 :=
  ⟨by linarith [Real.log_two_gt_d9], by linarith [Real.log_two_lt_d9]⟩

lemma h_bd : 1 / 4 ≤ Real.log (4 / 3) ∧ Real.log (4 / 3) ≤ 1 / 3 := by
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    have e : (1 : ℝ) - (4 / 3)⁻¹ = 1 / 4 := by norm_num
    rw [e] at h; exact h
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    linarith

lemma log34 : Real.log (3 / 4) = - Real.log (4 / 3) := by
  rw [show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, Real.log_inv]

lemma log4_eq : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

lemma log3_eq : Real.log 3 = 2 * Real.log 2 - Real.log (4 / 3) := by
  rw [Real.log_div (by norm_num) (by norm_num), log4_eq]; ring

lemma pow_eq_exp (b : ℝ) (hb : 0 < b) (n : ℕ) : b ^ n = Real.exp (n * Real.log b) := by
  rw [Real.exp_nat_mul, Real.exp_log hb]

lemma pDL (x u : ℝ) (hu : 1000 ≤ u) (hx : Real.log x = u ^ 5) :
    pD x = 2 * u ^ 3 ∧ pL x = u := by
  have hu0 : 0 ≤ u := by linarith
  constructor
  · unfold pD
    rw [hx, ← Real.rpow_natCast u 5, ← Real.rpow_mul hu0, ← Real.rpow_natCast u 3]; norm_num
  · unfold pL
    rw [hx, ← Real.rpow_natCast u 5, ← Real.rpow_mul hu0]; norm_num

/-- Linear bounds on the parameters (atoms `U = log x`, `v = u^3`). -/
lemma num_x (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5) :
    1 ≤ x ∧ 0 ≤ pD x ∧ pD x = 2 * u ^ 3 ∧ pL x = u ∧ 1000000 * u ^ 3 ≤ Real.log x ∧
    u ≤ u ^ 3 ∧ 6.931 * (pn0 x : ℝ) ≤ Real.log x ∧ Real.log x ≤ 6.932 * ((pn0 x : ℝ) + 1) ∧
    0 ≤ pW x ∧ pW x ≤ 6 * u ^ 3 ∧ 0 ≤ pWt x ∧ pWt x ≤ 8 * u ^ 3 ∧
    pW x + 2 * ((2 * pD x + 1) * Real.log 2) + 1 ≤ pm0 x * Real.log (4 / 3) ∧
    (pm0 x : ℝ) * Real.log (4 / 3) ≤ 13 * u ^ 3 ∧ (pm0 x : ℝ) ≤ 52 * u ^ 3 ∧ 1 ≤ pm0 x ∧
    u ≤ (pm0 x : ℝ) ∧ 2 * (pn0 x : ℝ) + pD x ≤ pK x ∧
    4 * pD x + 2 ≤ pDm x ∧ (pDm x : ℝ) ≤ 8 * u ^ 3 + 3 := by
  obtain ⟨hD, hL⟩ := pDL x u hu hx
  obtain ⟨l2a, l2b⟩ := l2_bd
  obtain ⟨ha, hb⟩ := h_bd
  have hu0 : 0 ≤ u := by linarith
  set v := u ^ 3 with hv
  have hv0 : 0 ≤ v := by positivity
  have hu2 : 1000000 ≤ u ^ 2 := by (first | linarith | nlinarith)
  have hvu : u ≤ v := by
    rw [hv, show u ^ 3 = u * u ^ 2 by ring]; (first | linarith [mul_le_mul_of_nonneg_left hu2 hu0] | nlinarith [mul_le_mul_of_nonneg_left hu2 hu0])
  have hU : Real.log x = u ^ 2 * v := by rw [hx, hv]; ring
  have hUv : 1000000 * v ≤ Real.log x := by rw [hU]; exact mul_le_mul_of_nonneg_right hu2 hv0
  have hx1 : 1 ≤ x := by
    rw [← Real.exp_log hx0]; exact Real.one_le_exp (by rw [hx]; positivity)
  have hl20 : 0 < 10 * Real.log 2 := by linarith
  have hn1 : (pn0 x : ℝ) ≤ Real.log x / (10 * Real.log 2) := Nat.floor_le (div_nonneg (by rw [hx]; positivity) hl20.le)
  have hn2 : Real.log x / (10 * Real.log 2) < pn0 x + 1 := Nat.lt_floor_add_one _
  rw [le_div_iff₀ hl20] at hn1
  rw [div_lt_iff₀ hl20] at hn2
  have hn0 : (0 : ℝ) ≤ pn0 x := Nat.cast_nonneg _
  have hn3 : 6.931 * (pn0 x : ℝ) ≤ Real.log x := by
    (first | linarith [mul_le_mul_of_nonneg_left l2a.le hn0] | nlinarith [mul_le_mul_of_nonneg_left l2a.le hn0])
  have hn4 : Real.log x ≤ 6.932 * ((pn0 x : ℝ) + 1) := by
    (first | linarith [mul_le_mul_of_nonneg_left l2b.le (by linarith : (0:ℝ) ≤ pn0 x + 1)] | nlinarith [mul_le_mul_of_nonneg_left l2b.le (by linarith : (0:ℝ) ≤ pn0 x + 1)])
  have hvl' : v * 0.6931 ≤ v * Real.log 2 := mul_le_mul_of_nonneg_left l2a.le hv0
  have hvl : v * Real.log 2 ≤ v * 0.6932 := mul_le_mul_of_nonneg_left l2b.le hv0
  have hW : pW x = 8 * (v * Real.log 2) + 2 * Real.log 2 + Real.log (4 / 3) := by
    unfold pW; rw [hD]; ring
  have hW0 : 0 ≤ pW x := by rw [hW]; linarith
  have hW1 : pW x ≤ 6 * v := by rw [hW]; linarith
  have hWt : pWt x = pW x + 2 * (v * Real.log 2) + Real.log 2 := by unfold pWt; rw [hD]; ring
  have hX : pW x + 2 * ((2 * pD x + 1) * Real.log 2) + 1 =
      pW x + 8 * (v * Real.log 2) + 2 * Real.log 2 + 1 := by rw [hD]; ring
  have hh0 : 0 < Real.log (4 / 3) := by linarith
  have hm1 : (pW x + 2 * ((2 * pD x + 1) * Real.log 2) + 1) / Real.log (4 / 3) ≤ pm0 x :=
    Nat.le_ceil _
  have hm2 : (pm0 x : ℝ) < (pW x + 2 * ((2 * pD x + 1) * Real.log 2) + 1) / Real.log (4 / 3) + 1 :=
    Nat.ceil_lt_add_one (by rw [hX]; positivity)
  rw [div_le_iff₀ hh0] at hm1
  have hm2' : (pm0 x : ℝ) * Real.log (4 / 3) <
      pW x + 2 * ((2 * pD x + 1) * Real.log 2) + 1 + Real.log (4 / 3) := by
    have := mul_lt_mul_of_pos_right hm2 hh0
    rwa [add_mul, div_mul_cancel₀ _ hh0.ne', one_mul] at this
  have hm0 : (0 : ℝ) ≤ pm0 x := Nat.cast_nonneg _
  have hmh : (pm0 x : ℝ) * Real.log (4 / 3) ≤ 13 * v := by rw [hX] at hm2'; linarith
  have hmlo : 5 * v ≤ (pm0 x : ℝ) * Real.log (4 / 3) := by rw [hX] at hm1; linarith
  have hq1 := mul_le_mul_of_nonneg_left ha hm0
  have hq2 := mul_le_mul_of_nonneg_left hb hm0
  have hm52 : (pm0 x : ℝ) ≤ 52 * v := by linarith
  have hmu : u ≤ (pm0 x : ℝ) := by linarith
  have hm1' : 1 ≤ pm0 x := by
    have : (1 : ℝ) ≤ pm0 x := by linarith
    exact_mod_cast this
  have hK : 2 * (pn0 x : ℝ) + pD x ≤ pK x := Nat.le_ceil _
  have hDm1 : 4 * pD x + 2 ≤ pDm x := Nat.le_ceil _
  have hDm2 : (pDm x : ℝ) ≤ 8 * v + 3 := by
    unfold pDm; rw [hD]
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 4 * (2 * v) + 2 by positivity)
    linarith
  refine ⟨hx1, by rw [hD]; positivity, hD, hL, hUv, hvu, hn3, hn4, hW0, hW1, ?_, ?_, hm1, hmh, hm52,
    hm1', hmu, hK, hDm1, hDm2⟩
  · rw [hWt]; have := mul_nonneg hv0 (Real.log_nonneg one_le_two); linarith
  · rw [hWt]; linarith

/-- `ε`, `hsize`, `hCL`, `m0 ≤ n0`. -/
lemma num_x2 (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5) :
    0 ≤ peps x ∧ peps x * u ≤ 1 ∧ peps x ≤ 1 ∧ 2 * (3 / 2 : ℝ) ^ (pn0 x) ≤ peps x * x ∧
    4 * (3 : ℝ) ^ (pn0 x + pm0 x) * 2 ^ (pDm x) ≤ x ∧
    1 * (Real.sqrt (pn0 x * pL x) + pL x) ≤ pD x ∧ pm0 x ≤ pn0 x := by
  obtain ⟨hx1, -, hD, hL, hUv, hvu, hn3, hn4, -, -, -, -, -, -, hm52, -, -, -, -, hDm2⟩ :=
    num_x x u hu hx0 hx
  obtain ⟨l2a, l2b⟩ := l2_bd
  obtain ⟨ha, hb⟩ := h_bd
  have hu0 : 0 < u := by linarith
  set v := u ^ 3 with hv
  have hv0 : 0 ≤ v := by positivity
  have hn0 : (0 : ℝ) ≤ pn0 x := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ pm0 x := Nat.cast_nonneg _
  have hDm0 : (0 : ℝ) ≤ pDm x := Nat.cast_nonneg _
  have hxe : Real.exp (Real.log x) = x := Real.exp_log hx0
  have hbig : 2 * (3 / 2 : ℝ) ^ (pn0 x) * u ≤ x := by
    have h1 : 2 * (3 / 2 : ℝ) ^ (pn0 x) * u ≤ 2 * 2 ^ (pn0 x) * u := by gcongr; norm_num
    have h2 : 2 * (2 : ℝ) ^ (pn0 x) * u =
        Real.exp (Real.log 2 + pn0 x * Real.log 2 + Real.log u) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
        ← pow_eq_exp 2 (by norm_num), Real.exp_log hu0]
    have h3 := Real.log_le_sub_one_of_pos hu0
    have h4 := mul_le_mul_of_nonneg_left l2b.le hn0
    refine h1.trans (h2.trans_le ((Real.exp_le_exp.mpr ?_).trans hxe.le))
    linarith
  have hepsx : peps x * x = 2 * (3 / 2 : ℝ) ^ (pn0 x) := by
    unfold peps; exact div_mul_cancel₀ _ hx0.ne'
  have heps0 : 0 ≤ peps x := by unfold peps; positivity
  have hepsu : peps x * u ≤ 1 := by
    have : peps x * u * x ≤ 1 * x := by
      rw [mul_right_comm, hepsx, one_mul]; exact hbig
    exact le_of_mul_le_mul_right this hx0
  have heps1 : peps x ≤ 1 := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ u by linarith) heps0
    linarith
  have hsize : 4 * (3 : ℝ) ^ (pn0 x + pm0 x) * 2 ^ (pDm x) ≤ x := by
    have e : 4 * (3 : ℝ) ^ (pn0 x + pm0 x) * 2 ^ (pDm x) = Real.exp (Real.log 4 +
        ((pn0 x + pm0 x : ℕ) : ℝ) * Real.log 3 + (pDm x : ℝ) * Real.log 2) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), ← pow_eq_exp 3 (by norm_num),
        ← pow_eq_exp 2 (by norm_num)]
    rw [e]
    refine (Real.exp_le_exp.mpr ?_).trans hxe.le
    have hl3 : Real.log 3 ≤ 1.1365 := by rw [log3_eq]; linarith
    have q1 := mul_le_mul_of_nonneg_left hl3 (by positivity : (0 : ℝ) ≤ ((pn0 x + pm0 x : ℕ) : ℝ))
    have q2 := mul_le_mul_of_nonneg_left l2b.le hDm0
    push_cast at q1 ⊢
    rw [log4_eq]
    linarith
  have hCL : 1 * (Real.sqrt (pn0 x * pL x) + pL x) ≤ pD x := by
    rw [hL, hD]
    have hnu : (pn0 x : ℝ) ≤ u ^ 5 := by rw [← hx]; linarith
    have hnu2 : (pn0 x : ℝ) * u ≤ v ^ 2 := by
      rw [hv, show (u ^ 3) ^ 2 = u ^ 5 * u by ring]
      exact mul_le_mul_of_nonneg_right hnu hu0.le
    have hs : Real.sqrt (pn0 x * u) ≤ v :=
      (Real.sqrt_le_sqrt hnu2).trans_eq (Real.sqrt_sq hv0)
    linarith
  have hmn : pm0 x ≤ pn0 x := by
    have : (pm0 x : ℝ) ≤ pn0 x := by linarith
    exact_mod_cast this
  exact ⟨heps0, hepsu, heps1, hepsx.ge, hsize, hCL, hmn⟩

/-- The `y`-dependent hypotheses of `p120_y` at `y = x^a`, `α ≤ a ≤ α²`. -/
lemma num_y (x u a : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5)
    (ha1 : 1001 / 1000 ≤ a) (ha2 : a ≤ 1002001 / 1000000) :
    16 ≤ x ^ a ∧ x ≤ x ^ a ∧ x ^ a + 1 ≤ (x ^ a) ^ alph ∧ (4 : ℝ) ^ (pn0 x) ≤ x ^ a ∧
    alph * Real.log (x ^ a) + pn0 x * Real.log (3 / 4) + (2 * pD x + 1) * Real.log 2 ≤ Real.log x ∧
    (pm0 x + 1) * Real.log (4 / 3) + (2 * pD x + 1) * Real.log 2 ≤ Real.log (x ^ a) - Real.log x ∧
    2 * pm0 x * Real.log (4 / 3) ≤ Real.log (x ^ a) - Real.log x + pWt x ∧
    2 * pWt x ≤ Real.log (x ^ a) - Real.log x + pWt x ∧
    Real.log (x ^ a) - Real.log x + pWt x ≤ alph * Real.log (x ^ a) - Real.log x - pWt x ∧
    alph * Real.log (x ^ a) - Real.log x - pWt x ≤ pn0 x * Real.log (4 / 3) ∧
    4 ≤ (alph - 1) * Real.log (x ^ a) := by
  obtain ⟨hx1, -, hD, -, hUv, hvu, hn3, hn4, -, -, hWt0, hWt1, -, hmh, -, -, -, -, -, -⟩ :=
    num_x x u hu hx0 hx
  obtain ⟨l2a, l2b⟩ := l2_bd
  obtain ⟨ha, hb⟩ := h_bd
  have hu0 : 0 < u := by linarith
  set v := u ^ 3 with hv
  have hv0 : 0 ≤ v := by positivity
  have hv1 : 1000 ≤ v := by linarith
  have hn0 : (0 : ℝ) ≤ pn0 x := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ pm0 x := Nat.cast_nonneg _
  set U := Real.log x with hU
  have hU0 : 0 ≤ U := by linarith
  have hY : Real.log (x ^ a) = a * U := Real.log_rpow hx0 a
  have hY1 : 1001 / 1000 * U ≤ a * U := mul_le_mul_of_nonneg_right ha1 hU0
  have hY2 : a * U ≤ 1002001 / 1000000 * U := mul_le_mul_of_nonneg_right ha2 hU0
  have halph : alph = 1001 / 1000 := rfl
  have hvl := mul_le_mul_of_nonneg_left l2b.le hv0
  have hnh := mul_le_mul_of_nonneg_left ha hn0
  have hxa : x ≤ x ^ a := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ a := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hxe : Real.exp U = x := Real.exp_log hx0
  have h16 : 16 ≤ x := by
    rw [← hxe]; have := Real.add_one_le_exp U; linarith
  have hy0 : 0 < x ^ a := by positivity
  have hgap : x ^ a + 1 ≤ (x ^ a) ^ alph := by
    rw [halph, show (1001 / 1000 : ℝ) = 1 + 1 / 1000 by norm_num, Real.rpow_add hy0,
      Real.rpow_one, Real.rpow_def_of_pos hy0, hY]
    have he := Real.add_one_le_exp (a * U * (1 / 1000))
    have h2e : 2 ≤ Real.exp (a * U * (1 / 1000)) := by linarith
    have := mul_le_mul_of_nonneg_left h2e hy0.le
    linarith
  have h4 : (4 : ℝ) ^ (pn0 x) ≤ x ^ a := by
    rw [pow_eq_exp 4 (by norm_num), log4_eq]
    refine le_trans ?_ (hxe.le.trans hxa)
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left l2b.le hn0
    (first | linarith | nlinarith)
  rw [hY, halph, log34, hD]
  refine ⟨by linarith, hxa, hgap, h4, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith⟩

lemma six_exp (u : ℝ) (hu : 0 ≤ u) : u ^ 6 * Real.exp (-u / 24) ≤ 137594142720 := by
  have h := Real.pow_div_factorial_le_exp (u / 24) (by positivity) 6
  rw [div_le_iff₀ (by positivity)] at h
  norm_num [Nat.factorial] at h
  have e1 : (u / 24) ^ 6 = u ^ 6 / 191102976 := by ring
  rw [e1] at h
  have e2 : Real.exp (-u / 24) * Real.exp (u / 24) = 1 := by
    rw [← Real.exp_add, show -u / 24 + u / 24 = 0 by ring, Real.exp_zero]
  have e3 : 0 ≤ Real.exp (-u / 24) := (Real.exp_pos _).le
  have f := mul_le_mul_of_nonneg_left h e3
  (first | linarith | nlinarith)

/-- `T / ly ≤ c / u` once `T ≤ c u^3` and `ly ≥ u^5 / 1000`. -/
lemma tv (T c u ly : ℝ) (hu : 1000 ≤ u) (hly : u ^ 5 / 1000 ≤ ly) (hT : T ≤ c * u ^ 3) (hc : 0 ≤ c) :
    T / ly ≤ c / u := by
  have hu0 : 0 < u := by linarith
  have hly0 : 0 < ly := lt_of_lt_of_le (by positivity) hly
  rw [div_le_div_iff₀ hly0 hu0]
  have h4 : u ^ 4 ≤ u ^ 5 / 1000 := by
    have := mul_le_mul_of_nonneg_right hu (by positivity : (0 : ℝ) ≤ u ^ 4)
    have e : u * u ^ 4 = u ^ 5 := by ring
    linarith
  have f1 := mul_le_mul_of_nonneg_right hT hu0.le
  have f2 := mul_le_mul_of_nonneg_left (h4.trans hly) hc
  have e : c * u ^ 3 * u = c * u ^ 4 := by ring
  linarith

/-- The `py_close` error of `p120_y`, with the parameters plugged in, is `≤ 5500/u + 20 eb`. -/
lemma err_gen (ε eb Wt Λ ly h u : ℝ) (hu : 1000 ≤ u) (hly : u ^ 5 / 1000 ≤ ly)
    (hε0 : 0 ≤ ε) (hεu : ε * u ≤ 1) (hε1 : ε ≤ 1) (heb : 0 ≤ eb) (hWt0 : 0 ≤ Wt)
    (hWt : Wt ≤ 8 * u ^ 3) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ 4) (ha : 1 / 4 ≤ h) (hb : h ≤ 1 / 3) :
    (4 * (ε * (ly / h + 1) * 4 + (ly / h + 1) * eb + (1 + ε) * (2 * (2 * Wt / h + 1)) * 4) / ly +
      Λ * (4 * ((2 * Wt / h + 1) + 2 / h) / ly)) ≤ 5500 / u + 20 * eb := by
  have hu0 : 0 < u := by linarith
  have hu5 : 1000000000000 ≤ u ^ 5 / 1000 := by
    have : (1000 : ℝ) ^ 5 ≤ u ^ 5 := pow_le_pow_left₀ (by norm_num) hu 5
    linarith
  have hly1 : 1 ≤ ly := by linarith
  have hly0 : 0 < ly := by linarith
  have hh0 : 0 < h := by linarith
  have hP : ly / h + 1 ≤ 5 * ly := by
    have : ly / h ≤ 4 * ly := by
      rw [div_le_iff₀ hh0]; (first | linarith | nlinarith)
    linarith
  have hP0 : 0 ≤ ly / h + 1 := by positivity
  have hQ1 : 2 * Wt / h ≤ 64 * u ^ 3 := by
    rw [div_le_iff₀ hh0]; (first | linarith [mul_le_mul_of_nonneg_left ha hWt0] | nlinarith [mul_le_mul_of_nonneg_left ha hWt0])
  have hu3 : 1 ≤ u ^ 3 := by (first | linarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (by linarith : (1:ℝ) ≤ u) 3] | nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (by linarith : (1:ℝ) ≤ u) 3])
  have h2h : 2 / h ≤ 8 := by rw [div_le_iff₀ hh0]; linarith
  set P := ly / h + 1 with hPdef
  set Q := 2 * Wt / h + 1 with hQdef
  have hQ0 : 0 ≤ Q := by rw [hQdef]; positivity
  have hQly : Q / ly ≤ 65 / u := tv Q 65 u ly hu hly (by linarith) (by norm_num)
  have hQ2ly : (Q + 2 / h) / ly ≤ 73 / u := tv _ 73 u ly hu hly (by linarith) (by norm_num)
  have hBIG : 4 * (ε * P * 4 + P * eb + (1 + ε) * (2 * Q) * 4) ≤ 80 * ε * ly + 20 * eb * ly + 64 * Q := by
    have f1 := mul_le_mul_of_nonneg_left hP hε0
    have f2 := mul_le_mul_of_nonneg_right hP heb
    have f3 := mul_le_mul_of_nonneg_right (show 1 + ε ≤ 2 by linarith) (by positivity : (0 : ℝ) ≤ 2 * Q)
    linarith
  have hT1 : 4 * (ε * P * 4 + P * eb + (1 + ε) * (2 * Q) * 4) / ly ≤
      80 * ε + 20 * eb + 64 * (Q / ly) := by
    calc _ ≤ (80 * ε * ly + 20 * eb * ly + 64 * Q) / ly := div_le_div_of_nonneg_right hBIG hly0.le
      _ = 80 * ε + 20 * eb + 64 * (Q / ly) := by field_simp <;> ring
  have hT2 : Λ * (4 * (Q + 2 / h) / ly) ≤ 4 * (4 * (73 / u)) := by
    rw [mul_div_assoc]
    have h0 : 0 ≤ (Q + 2 / h) / ly := by positivity
    have := mul_le_mul hΛ (mul_le_mul_of_nonneg_left hQ2ly (by norm_num : (0:ℝ) ≤ 4))
      (by positivity) (by norm_num)
    linarith
  have hεu' : ε ≤ 1 / u := by rw [le_div_iff₀ hu0]; exact hεu
  have e1 : 80 * (1 / u) + 64 * (65 / u) + 4 * (4 * (73 / u)) = 5408 / u := by ring
  have e2 : (5408 : ℝ) / u ≤ 5500 / u := div_le_div_of_nonneg_right (by norm_num) hu0.le
  linarith

/-- `eb` of `p120_y` with the parameters plugged in (`C = 1`, `A' = 1`, `L = u`). -/
lemma eb_bound (x u Cosc : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5)
    (hCosc : 0 ≤ Cosc) :
    4 * ((pn0 x : ℝ) * (1 / 2) ^ (pK x) + Cosc * (pm0 x : ℝ) ^ (-(1 : ℝ)) +
      2 * pn0 x * Real.exp (-(1 * pL x) / 24)) ≤ 4 * (1 + Cosc + 2 * 137594142720) / u := by
  obtain ⟨-, hD0, -, hL, hUv, hvu, hn3, hn4, -, -, -, -, -, -, -, -, hmu, hK, -, -⟩ :=
    num_x x u hu hx0 hx
  have hu0 : 0 < u := by linarith
  have hn0 : (0 : ℝ) ≤ pn0 x := Nat.cast_nonneg _
  have hun : u ≤ (pn0 x : ℝ) := by (first | linarith | nlinarith)
  have hnu5 : (pn0 x : ℝ) ≤ u ^ 5 := by rw [← hx]; linarith
  -- (a)
  have hK2 : 2 * pn0 x ≤ pK x := by
    have : ((2 * pn0 x : ℕ) : ℝ) ≤ pK x := by push_cast; linarith
    exact_mod_cast this
  have hsq : ((pn0 x : ℝ)) ^ 2 ≤ (4 : ℝ) ^ (pn0 x) := by
    have h1 : pn0 x < 2 ^ pn0 x := by
      first | exact Nat.lt_two_pow_self | exact Nat.lt_two_pow_self _ | exact Nat.lt_two_pow _
    have h2 : pn0 x ^ 2 ≤ 4 ^ pn0 x := by
      calc pn0 x ^ 2 ≤ (2 ^ pn0 x) ^ 2 := Nat.pow_le_pow_left h1.le 2
        _ = 4 ^ pn0 x := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    exact_mod_cast h2
  have ha : (pn0 x : ℝ) * (1 / 2) ^ (pK x) ≤ 1 / u := by
    rw [le_div_iff₀ hu0]
    have hp : ((1 : ℝ) / 2) ^ (pK x) ≤ (1 / 4) ^ (pn0 x) := by
      calc ((1 : ℝ) / 2) ^ (pK x) ≤ (1 / 2) ^ (2 * pn0 x) :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hK2
        _ = (1 / 4) ^ (pn0 x) := by rw [pow_mul]; norm_num
    have h14 : (0 : ℝ) ≤ (1 / 4) ^ (pn0 x) := by positivity
    calc (pn0 x : ℝ) * (1 / 2) ^ (pK x) * u ≤ (pn0 x : ℝ) * (1 / 4) ^ (pn0 x) * pn0 x := by
          gcongr
      _ = (pn0 x : ℝ) ^ 2 * (1 / 4) ^ (pn0 x) := by ring
      _ ≤ (4 : ℝ) ^ (pn0 x) * (1 / 4) ^ (pn0 x) := mul_le_mul_of_nonneg_right hsq h14
      _ = 1 := by rw [← mul_pow]; norm_num
  -- (b)
  have hb : Cosc * (pm0 x : ℝ) ^ (-(1 : ℝ)) ≤ Cosc / u := by
    rw [Real.rpow_neg_one, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ hCosc
    first | exact inv_anti₀ hu0 hmu | exact inv_le_inv_of_le hu0 hmu
  -- (c)
  have hc : 2 * pn0 x * Real.exp (-(1 * pL x) / 24) ≤ 2 * 137594142720 / u := by
    rw [hL, one_mul, le_div_iff₀ hu0]
    have h6 := six_exp u hu0.le
    have he : 0 ≤ Real.exp (-u / 24) := (Real.exp_pos _).le
    have f1 : (pn0 x : ℝ) * u ≤ u ^ 6 := by
      have := mul_le_mul_of_nonneg_right hnu5 hu0.le
      have e : u ^ 5 * u = u ^ 6 := by ring
      linarith
    have f2 := mul_le_mul_of_nonneg_right f1 he
    (first | linarith | nlinarith)
  have e : 4 * (1 + Cosc + 2 * 137594142720) / u = 4 * (1 / u + Cosc / u + 2 * 137594142720 / u) := by
    ring
  rw [e]
  linarith

/-- The `p512` deviation bound is `≤ (8 + 2 B)/u`. -/
lemma dev_bound (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5) :
    8 * x ^ (-(1 / 20000 : ℝ)) + 2 * Real.log x * Real.exp (-(Real.log x ^ ((1 : ℝ) / 5)) / 24) ≤
      (8 + 2 * 137594142720) / u := by
  have hL := (pDL x u hu hx).2
  unfold pL at hL
  have hu0 : 0 < u := by linarith
  rw [hL, Real.rpow_def_of_pos hx0, hx]
  have h1 : Real.exp (u ^ 5 * -(1 / 20000)) ≤ 1 / u := by
    rw [le_div_iff₀ hu0]
    have hb := Real.add_one_le_exp (u ^ 5 / 20000)
    have h5 : u ≤ u ^ 5 / 20000 := by
      have h4 : (1000 : ℝ) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) hu 4
      have := mul_le_mul_of_nonneg_left h4 hu0.le
      have e : u * u ^ 4 = u ^ 5 := by ring
      linarith
    have e : Real.exp (u ^ 5 * -(1 / 20000)) * Real.exp (u ^ 5 / 20000) = 1 := by
      rw [← Real.exp_add, show u ^ 5 * -(1 / 20000) + u ^ 5 / 20000 = 0 by ring, Real.exp_zero]
    have he : 0 ≤ Real.exp (u ^ 5 * -(1 / 20000)) := (Real.exp_pos _).le
    have := mul_le_mul_of_nonneg_left (show u ≤ Real.exp (u ^ 5 / 20000) by linarith) he
    linarith
  have h2 : 2 * u ^ 5 * Real.exp (-u / 24) ≤ 2 * 137594142720 / u := by
    rw [le_div_iff₀ hu0]
    have := six_exp u hu0.le
    have e : 2 * u ^ 5 * Real.exp (-u / 24) * u = 2 * (u ^ 6 * Real.exp (-u / 24)) := by ring
    rw [e]; linarith
  have e : (8 + 2 * 137594142720) / u = 8 * (1 / u) + 2 * 137594142720 / u := by ring
  rw [e]; linarith

end Num120

end Tao31

open Tao31 in
theorem solution :
    ∀ (pn0 : ℝ → ℕ) (pD pL pW pWt peps : ℝ → ℝ) (pm0 pK pDm : ℝ → ℕ),
    (∀ x, pn0 x = ⌊Real.log x / (10 * Real.log 2)⌋₊) →
    (∀ x, pD x = 2 * Real.log x ^ ((3 : ℝ) / 5)) →
    (∀ x, pL x = Real.log x ^ ((1 : ℝ) / 5)) →
    (∀ x, pW x = 2 * ((2 * pD x + 1) * Real.log 2) + Real.log (4 / 3)) →
    (∀ x, pWt x = pW x + pD x * Real.log 2 + Real.log 2) →
    (∀ x, peps x = 2 * (3 / 2 : ℝ) ^ (pn0 x) / x) →
    (∀ x, pm0 x = ⌈(pW x + 2 * ((2 * pD x + 1) * Real.log 2) + 1) / Real.log (4 / 3)⌉₊) →
    (∀ x, pK x = ⌈2 * (pn0 x : ℝ) + pD x⌉₊) →
    (∀ x, pDm x = ⌈4 * pD x + 2⌉₊) →
    (∀ (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5),
      1 ≤ x ∧ 0 ≤ pD x ∧ pD x = 2 * u ^ 3 ∧ pL x = u ∧ 1000000 * u ^ 3 ≤ Real.log x ∧
    u ≤ u ^ 3 ∧ 6.931 * (pn0 x : ℝ) ≤ Real.log x ∧ Real.log x ≤ 6.932 * ((pn0 x : ℝ) + 1) ∧
    0 ≤ pW x ∧ pW x ≤ 6 * u ^ 3 ∧ 0 ≤ pWt x ∧ pWt x ≤ 8 * u ^ 3 ∧
    pW x + 2 * ((2 * pD x + 1) * Real.log 2) + 1 ≤ pm0 x * Real.log (4 / 3) ∧
    (pm0 x : ℝ) * Real.log (4 / 3) ≤ 13 * u ^ 3 ∧ (pm0 x : ℝ) ≤ 52 * u ^ 3 ∧ 1 ≤ pm0 x ∧
    u ≤ (pm0 x : ℝ) ∧ 2 * (pn0 x : ℝ) + pD x ≤ pK x ∧
    4 * pD x + 2 ≤ pDm x ∧ (pDm x : ℝ) ≤ 8 * u ^ 3 + 3) ∧
    (∀ (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5),
      0 ≤ peps x ∧ peps x * u ≤ 1 ∧ peps x ≤ 1 ∧ 2 * (3 / 2 : ℝ) ^ (pn0 x) ≤ peps x * x ∧
    4 * (3 : ℝ) ^ (pn0 x + pm0 x) * 2 ^ (pDm x) ≤ x ∧
    1 * (Real.sqrt (pn0 x * pL x) + pL x) ≤ pD x ∧ pm0 x ≤ pn0 x) ∧
    (∀ (x u a : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5) (ha1 : 1001 / 1000 ≤ a) (ha2 : a ≤ 1002001 / 1000000),
      16 ≤ x ^ a ∧ x ≤ x ^ a ∧ x ^ a + 1 ≤ (x ^ a) ^ ((1001 : ℝ) / 1000) ∧ (4 : ℝ) ^ (pn0 x) ≤ x ^ a ∧
    ((1001 : ℝ) / 1000) * Real.log (x ^ a) + pn0 x * Real.log (3 / 4) + (2 * pD x + 1) * Real.log 2 ≤ Real.log x ∧
    (pm0 x + 1) * Real.log (4 / 3) + (2 * pD x + 1) * Real.log 2 ≤ Real.log (x ^ a) - Real.log x ∧
    2 * pm0 x * Real.log (4 / 3) ≤ Real.log (x ^ a) - Real.log x + pWt x ∧
    2 * pWt x ≤ Real.log (x ^ a) - Real.log x + pWt x ∧
    Real.log (x ^ a) - Real.log x + pWt x ≤ ((1001 : ℝ) / 1000) * Real.log (x ^ a) - Real.log x - pWt x ∧
    ((1001 : ℝ) / 1000) * Real.log (x ^ a) - Real.log x - pWt x ≤ pn0 x * Real.log (4 / 3) ∧
    4 ≤ (((1001 : ℝ) / 1000) - 1) * Real.log (x ^ a)) ∧
    (∀ (ε eb Wt Λ ly h u : ℝ) (hu : 1000 ≤ u) (hly : u ^ 5 / 1000 ≤ ly) (hε0 : 0 ≤ ε) (hεu : ε * u ≤ 1) (hε1 : ε ≤ 1) (heb : 0 ≤ eb) (hWt0 : 0 ≤ Wt) (hWt : Wt ≤ 8 * u ^ 3) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ 4) (ha : 1 / 4 ≤ h) (hb : h ≤ 1 / 3),
      (4 * (ε * (ly / h + 1) * 4 + (ly / h + 1) * eb + (1 + ε) * (2 * (2 * Wt / h + 1)) * 4) / ly +
      Λ * (4 * ((2 * Wt / h + 1) + 2 / h) / ly)) ≤ 5500 / u + 20 * eb) ∧
    (∀ (x u Cosc : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5) (hCosc : 0 ≤ Cosc),
      4 * ((pn0 x : ℝ) * (1 / 2) ^ (pK x) + Cosc * (pm0 x : ℝ) ^ (-(1 : ℝ)) +
      2 * pn0 x * Real.exp (-(1 * pL x) / 24)) ≤ 4 * (1 + Cosc + 2 * 137594142720) / u) ∧
    (∀ (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5),
      8 * x ^ (-(1 / 20000 : ℝ)) + 2 * Real.log x * Real.exp (-(Real.log x ^ ((1 : ℝ) / 5)) / 24) ≤
      (8 + 2 * 137594142720) / u) := by
  intro pn0 pD pL pW pWt peps pm0 pK pDm hn0 hD hL hW hWt heps hm0 hK hDm
  obtain rfl : pn0 = Tao31.pn0 := funext hn0
  obtain rfl : pD = Tao31.pD := funext hD
  obtain rfl : pL = Tao31.pL := funext hL
  obtain rfl : pW = Tao31.pW := funext hW
  obtain rfl : pWt = Tao31.pWt := funext hWt
  obtain rfl : peps = Tao31.peps := funext heps
  obtain rfl : pm0 = Tao31.pm0 := funext hm0
  obtain rfl : pK = Tao31.pK := funext hK
  obtain rfl : pDm = Tao31.pDm := funext hDm
  exact ⟨Tao31.num_x, Tao31.num_x2, Tao31.num_y, Tao31.err_gen, Tao31.eb_bound, Tao31.dev_bound⟩
