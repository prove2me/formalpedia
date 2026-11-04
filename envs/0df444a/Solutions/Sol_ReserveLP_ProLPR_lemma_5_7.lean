-- Prove2me | solution 1 for ReserveLP.ProLPR.lemma_5_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T09:42:20.631689+00:00
-- url     : https://prove2.me/submissions/3329da39-943f-4a14-8d52-9e0b7d18e88c

import Mathlib
import Definitions.Def_ReserveLP_ProLPR_Model

open ReserveLP.ProLPR Finset

theorem rlp57_log (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    v + v ^ 2 / 2 + v ^ 3 / 3 ≤ -Real.log (1 - v) := by
  have habs : |v| < 1 := by rw [abs_of_nonneg hv0]; exact hv1
  have h := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have := sum_le_hasSum (range 3) (fun i _ => by positivity) h
  simp [sum_range_succ] at this
  norm_num at this
  linarith

theorem rlp57_a (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    1 + 2 * θ ≤ 1.2534 * (1 + θ + θ^2/2 + θ^3/6 + θ^4/24 + θ^5/120) := by
  nlinarith [sq_nonneg (θ - 1/2), mul_nonneg h0 (sub_nonneg.mpr h1), pow_nonneg h0 3,
    pow_nonneg h0 4, pow_nonneg h0 5]

theorem rlp57_b (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    1 + 3 * θ / 2 ≤ 1.2534 * (1 + θ + θ^2/2 + θ^3/6 + θ^4/24 + θ^5/120) *
      (1 - θ/2 + θ^2/2 - θ^3/12 - θ^4/12) := by
  nlinarith [sq_nonneg (θ - 1/2), mul_nonneg h0 (sub_nonneg.mpr h1), pow_nonneg h0 3,
    pow_nonneg h0 4, pow_nonneg h0 5, mul_nonneg (pow_nonneg h0 2) (sub_nonneg.mpr h1),
    mul_nonneg (pow_nonneg h0 3) (sub_nonneg.mpr h1), mul_nonneg (pow_nonneg h0 4) (sub_nonneg.mpr h1),
    mul_nonneg (mul_nonneg h0 (sub_nonneg.mpr h1)) (sq_nonneg (θ - 1/2))]

theorem rlp57_c (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (1 - 2*θ/3)^2 * (1 + 4*θ/3) * (1 + θ + θ^2/2 + θ^3/6 + θ^4/24 + θ^5/120 + θ^6 * 7/4320)
      ≤ 1.2534 := by
  nlinarith [sq_nonneg (θ - 2/5), mul_nonneg h0 (sub_nonneg.mpr h1), pow_nonneg h0 3,
    pow_nonneg h0 4, pow_nonneg h0 5, mul_nonneg (pow_nonneg h0 2) (sub_nonneg.mpr h1),
    mul_nonneg (pow_nonneg h0 3) (sub_nonneg.mpr h1), mul_nonneg (pow_nonneg h0 4) (sub_nonneg.mpr h1),
    mul_nonneg (mul_nonneg h0 (sub_nonneg.mpr h1)) (sq_nonneg (θ - 2/5))]

/-- The two-variable polynomial inequality for `k ≥ 4`, via concavity in `u`. -/
theorem rlp57_poly (θ u : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hu0 : 0 ≤ u) (hu : u ≤ θ / 2) :
    1 - u + 2 * θ ≤ 1.2534 * (1 + θ + θ^2/2 + θ^3/6 + θ^4/24 + θ^5/120) *
      ((1 - u) * (1 + (θ * u + 2/3 * θ * u ^ 2))) := by
  set A := 1.2534 * (1 + θ + θ^2/2 + θ^3/6 + θ^4/24 + θ^5/120) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have ha := rlp57_a θ h0 h1
  have hb := rlp57_b θ h0 h1
  rw [← hA] at ha
  have hb' : 0 ≤ A * (1 - θ/2 + θ^2/2 - θ^3/12 - θ^4/12) - 3 * θ / 2 - 1 := by
    rw [hA]; linarith
  have hid : θ * (A * ((1 - u) * (1 + (θ * u + 2/3 * θ * u ^ 2))) - (1 - u + 2 * θ)) =
      (θ - 2 * u) * (A - 2 * θ - 1) +
      2 * u * (A * (1 - θ/2 + θ^2/2 - θ^3/12 - θ^4/12) - 3 * θ / 2 - 1) +
      A * θ ^ 2 * u * (θ - 2 * u) * (θ + 2 * u + 1) / 6 := by ring
  rcases h0.lt_or_eq with hθ | hθ
  · have hnn : 0 ≤ (θ - 2 * u) * (A - 2 * θ - 1) +
        2 * u * (A * (1 - θ/2 + θ^2/2 - θ^3/12 - θ^4/12) - 3 * θ / 2 - 1) +
        A * θ ^ 2 * u * (θ - 2 * u) * (θ + 2 * u + 1) / 6 := by
      have a1 : 0 ≤ (θ - 2 * u) * (A - 2 * θ - 1) := mul_nonneg (by linarith) (by linarith)
      have a2 := mul_nonneg (by linarith : (0:ℝ) ≤ 2 * u) hb'
      have a3 : 0 ≤ A * θ ^ 2 * u * (θ - 2 * u) * (θ + 2 * u + 1) / 6 := by
        have : 0 ≤ θ - 2 * u := by linarith
        have : 0 ≤ θ + 2 * u + 1 := by linarith
        positivity
      linarith
    rw [← hid] at hnn
    have := (mul_nonneg_iff_of_pos_left hθ).mp hnn
    linarith
  · subst hθ
    have : u = 0 := by linarith
    subst this; norm_num

theorem rlp57_K : (1.2534 : ℝ) ≤ 2 * (Real.sqrt 2 - 1) * Real.exp (Real.sqrt 2 - 1) := by
  set s := Real.sqrt 2 with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hslo : 1.4142135 ≤ s := by nlinarith
  have hx : 0 ≤ s - 1 := by linarith
  have hT := Real.sum_le_exp_of_nonneg hx 5
  simp [sum_range_succ, Nat.factorial] at hT
  norm_num at hT
  have key : 2 * (s - 1) * (1 + (s - 1) + (s - 1) ^ 2 / 2 + (s - 1) ^ 3 / 6 + (s - 1) ^ 4 / 24) =
      17 * s / 12 - 3 / 4 := by
    linear_combination (s ^ 3 / 12 - s ^ 2 / 12 + 2 * s / 3) * hs2
  have hT' : 1 + (s - 1) + (s - 1) ^ 2 / 2 + (s - 1) ^ 3 / 6 + (s - 1) ^ 4 / 24 ≤
      Real.exp (s - 1) := by linarith
  calc (1.2534 : ℝ) ≤ 17 * s / 12 - 3 / 4 := by linarith
    _ = 2 * (s - 1) * (1 + (s - 1) + (s - 1) ^ 2 / 2 + (s - 1) ^ 3 / 6 + (s - 1) ^ 4 / 24) := key.symm
    _ ≤ 2 * (s - 1) * Real.exp (s - 1) := mul_le_mul_of_nonneg_left hT' (by linarith)

theorem solution (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) (hk : 2 ≤ k) :
    OPT1 θ k ≤ cStar := by
  obtain ⟨h0, h1⟩ := hθ
  set s := Real.sqrt 2 with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 ≤ s := by nlinarith
  have hcs : cStar = Real.exp (-1) * (2 * (s - 1) * Real.exp (s - 1)) := by
    unfold cStar
    rw [← hs]
    have : Real.exp (s - 2) = Real.exp (-1) * Real.exp (s - 1) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  have hK := rlp57_K
  rw [← hs] at hK
  rw [hcs]
  have hem := Real.exp_pos (-1)
  -- reduce to `G * exp θ ≤ 2 θ0 exp θ0` where OPT1 = exp(θ-1) G
  have hred : ∀ G : ℝ, OPT1 θ k = Real.exp (θ - 1) * G →
      G * Real.exp θ ≤ 2 * (s - 1) * Real.exp (s - 1) →
      OPT1 θ k ≤ Real.exp (-1) * (2 * (s - 1) * Real.exp (s - 1)) := by
    intro G hG hle
    rw [hG]
    have : Real.exp (θ - 1) * G = Real.exp (-1) * (G * Real.exp θ) := by
      rw [show θ - 1 = -1 + θ by ring, Real.exp_add]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hle hem.le
  rcases (show k = 2 ∨ k = 3 ∨ 4 ≤ k by omega) with rfl | rfl | hk4
  · -- k = 2 : tangent-line argument
    apply hred ((1 - θ) * (1 + θ))
    · unfold OPT1; norm_num; ring
    · have htan : 1 + (s - 1 - θ) ≤ Real.exp (s - 1 - θ) := by
        linarith [Real.add_one_le_exp (s - 1 - θ)]
      have hpoly : (1 - θ) * (1 + θ) ≤ 2 * (s - 1) * (1 + (s - 1 - θ)) := by
        nlinarith [sq_nonneg (θ - (s - 1))]
      have : 2 * (s - 1) * (1 + (s - 1 - θ)) ≤ 2 * (s - 1) * Real.exp (s - 1 - θ) :=
        mul_le_mul_of_nonneg_left htan (by linarith)
      have e : Real.exp (s - 1 - θ) * Real.exp θ = Real.exp (s - 1) := by
        rw [← Real.exp_add]; ring_nf
      have hpos := Real.exp_pos θ
      calc (1 - θ) * (1 + θ) * Real.exp θ ≤ 2 * (s - 1) * Real.exp (s - 1 - θ) * Real.exp θ :=
            mul_le_mul_of_nonneg_right (hpoly.trans this) hpos.le
        _ = 2 * (s - 1) * Real.exp (s - 1) := by rw [mul_assoc, e]
  · -- k = 3 : explicit cubic against an upper Taylor bound of exp
    apply hred ((1 - 2*θ/3)^2 * (1 + 4*θ/3))
    · unfold OPT1; norm_num; ring
    · have hU := Real.exp_bound' h0 h1 (n := 6) (by norm_num)
      simp [sum_range_succ, Nat.factorial] at hU
      norm_num at hU
      have hG0 : 0 ≤ (1 - 2*θ/3)^2 * (1 + 4*θ/3) := by positivity
      have hc := rlp57_c θ h0 h1
      calc (1 - 2*θ/3)^2 * (1 + 4*θ/3) * Real.exp θ
          ≤ (1 - 2*θ/3)^2 * (1 + 4*θ/3) *
            (1 + θ + θ^2/2 + θ^3/6 + θ^4/24 + θ^5/120 + θ^6 * 7/4320) := by
            apply mul_le_mul_of_nonneg_left _ hG0; linarith
        _ ≤ 1.2534 := hc
        _ ≤ _ := hK
  · -- k ≥ 4
    have hk4' : (4 : ℝ) ≤ k := by exact_mod_cast hk4
    have hkpos : (0 : ℝ) < k := by linarith
    set u := 2 * θ / (k : ℝ) with hu
    have hu0 : 0 ≤ u := by positivity
    have huθ : u ≤ θ / 2 := by
      rw [hu, div_le_div_iff₀ hkpos (by norm_num)]; nlinarith
    have hu1 : u < 1 := by linarith
    have hku : (k : ℝ) * u = 2 * θ := by rw [hu]; field_simp
    have h1u : 0 < 1 - u := by linarith
    set y := θ * u + 2/3 * θ * u ^ 2 with hy
    have hy0 : 0 ≤ y := by positivity
    have hpow : (1 - u) ^ k ≤ Real.exp (-(2 * θ + y)) := by
      have e1 : (1 - u) ^ k = Real.exp (k * Real.log (1 - u)) := by
        rw [Real.exp_nat_mul, Real.exp_log h1u]
      rw [e1, Real.exp_le_exp]
      have : (k : ℝ) * (u + u ^ 2 / 2 + u ^ 3 / 3) = 2 * θ + y := by
        rw [hy]
        have : (k : ℝ) * (u + u ^ 2 / 2 + u ^ 3 / 3) = (k * u) * (1 + u / 2 + u ^ 2 / 3) := by ring
        rw [this, hku]; ring
      nlinarith [mul_le_mul_of_nonneg_left (rlp57_log u hu0 hu1) hkpos.le]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    set P := (1 - u) ^ k' with hP
    have hP0 : 0 ≤ P := pow_nonneg h1u.le _
    have hPk : (1 - u) ^ (k' + 1) = P * (1 - u) := pow_succ _ _
    apply hred (P * (1 - u + 2 * θ))
    · unfold OPT1; rw [← hu, Nat.add_sub_cancel, hP]; ring
    · have hpoly := rlp57_poly θ u h0 h1 hu0 huθ
      rw [← hy] at hpoly
      have hT := Real.sum_le_exp_of_nonneg h0 6
      simp [sum_range_succ, Nat.factorial] at hT
      norm_num at hT
      have hT5 : 1 + θ + θ^2/2 + θ^3/6 + θ^4/24 + θ^5/120 ≤ Real.exp θ := by linarith
      have hey : 1 + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
      have hPu : P * (1 - u) ≤ Real.exp (-(2 * θ + y)) := by rw [← hPk]; exact hpow
      -- (1 - u + 2θ) ≤ K e^θ (1-u) e^y
      have hstep : 1 - u + 2 * θ ≤ 2 * (s - 1) * Real.exp (s - 1) * Real.exp θ *
          ((1 - u) * Real.exp y) := by
        refine hpoly.trans ?_
        have hA : 1.2534 * (1 + θ + θ^2/2 + θ^3/6 + θ^4/24 + θ^5/120) ≤
            2 * (s - 1) * Real.exp (s - 1) * Real.exp θ :=
          mul_le_mul hK hT5 (by positivity)
            (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.exp_pos _).le)
        apply mul_le_mul hA _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hey h1u.le
      have hexp : Real.exp θ * Real.exp y * Real.exp (-(2 * θ + y)) = Real.exp (-θ) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      have hfin : P * (1 - u + 2 * θ) ≤ 2 * (s - 1) * Real.exp (s - 1) * Real.exp (-θ) := by
        calc P * (1 - u + 2 * θ) ≤ P * (2 * (s - 1) * Real.exp (s - 1) * Real.exp θ *
              ((1 - u) * Real.exp y)) := mul_le_mul_of_nonneg_left hstep hP0
          _ = 2 * (s - 1) * Real.exp (s - 1) * Real.exp θ * Real.exp y * (P * (1 - u)) := by ring
          _ ≤ 2 * (s - 1) * Real.exp (s - 1) * Real.exp θ * Real.exp y *
              Real.exp (-(2 * θ + y)) := by
            apply mul_le_mul_of_nonneg_left hPu
            have := Real.exp_pos (s - 1); have := Real.exp_pos θ; have := Real.exp_pos y
            have : 0 ≤ s - 1 := by linarith
            positivity
          _ = 2 * (s - 1) * Real.exp (s - 1) * Real.exp (-θ) := by
            rw [mul_assoc (2 * (s - 1) * Real.exp (s - 1) * Real.exp θ), mul_assoc
              (2 * (s - 1) * Real.exp (s - 1)), ← mul_assoc (Real.exp θ), hexp]
      have e2 : Real.exp (-θ) * Real.exp θ = 1 := by rw [← Real.exp_add]; simp
      calc P * (1 - u + 2 * θ) * Real.exp θ ≤
          2 * (s - 1) * Real.exp (s - 1) * Real.exp (-θ) * Real.exp θ :=
            mul_le_mul_of_nonneg_right hfin (Real.exp_pos θ).le
        _ = 2 * (s - 1) * Real.exp (s - 1) := by rw [mul_assoc, e2, mul_one]
-- x
