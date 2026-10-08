-- Prove2me | solution 1 for SolomonRWRE.SlowApproach.lemma_2_6
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:49:06.171722+00:00
-- url     : https://prove2.me/submissions/9bd888cc-5cbf-40e2-9625-3672739d4f84

import Mathlib
import Definitions.Def_SolomonRWRE_SlowApproach_Transforms
open Filter
open scoped Topology


namespace SolomonRWRE.SlowApproach

/-- the discriminant square root -/
lemma sqrt_disc_sq (θ u : ℝ) (hθ : 1 < θ) (hu : 0 ≤ u) :
    Real.sqrt ((θ + 1) ^ 2 - 4 * θ * Real.exp (-2 * u)) ^ 2
      = (θ + 1) ^ 2 - 4 * θ * Real.exp (-2 * u) := by
  apply Real.sq_sqrt
  have h1 : Real.exp (-2 * u) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  nlinarith

lemma lambda_mul (θ u : ℝ) (hθ : 1 < θ) (hu : 0 ≤ u) :
    lambdaOne θ u * lambdaTwo θ u = θ := by
  unfold lambdaOne lambdaTwo
  have hs := sqrt_disc_sq θ u hθ hu
  have he : Real.exp u ^ 2 * Real.exp (-2 * u) = 1 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    have : u + u + -2 * u = 0 := by ring
    rw [this, Real.exp_zero]
  linear_combination (Real.exp u ^ 2 / 4) * (-hs) + θ * he

lemma lambda_add (θ u : ℝ) :
    lambdaOne θ u + lambdaTwo θ u = Real.exp u * (θ + 1) := by
  unfold lambdaOne lambdaTwo; ring

lemma quad_factor (θ u z : ℝ) (hθ : 1 < θ) (hu : 0 ≤ u) :
    z ^ 2 - Real.exp u * (θ + 1) * z + θ = (z - lambdaOne θ u) * (z - lambdaTwo θ u) := by
  have h1 := lambda_mul θ u hθ hu
  have h2 := lambda_add θ u
  linear_combination z * h2 - h1

lemma lambdaOne_gt_one (θ u : ℝ) (hθ : 1 < θ) (hu : 0 ≤ u) : 1 < lambdaOne θ u := by
  unfold lambdaOne
  have h1 : 1 ≤ Real.exp u := Real.one_le_exp hu
  have h2 : 0 ≤ Real.sqrt ((θ + 1) ^ 2 - 4 * θ * Real.exp (-2 * u)) := Real.sqrt_nonneg _
  nlinarith

lemma lambdaTwo_lt_one (θ u : ℝ) (hθ : 1 < θ) (hu : 0 < u) : lambdaTwo θ u < 1 := by
  have hq := quad_factor θ u 1 hθ hu.le
  have he : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu
  have h1 := lambdaOne_gt_one θ u hθ hu.le
  have hneg : (1 - lambdaOne θ u) * (1 - lambdaTwo θ u) < 0 := by
    rw [← hq]; nlinarith
  by_contra hc
  push Not at hc
  nlinarith

/-- lower bound: `1 - c₂ u ≤ λ₂` with `c₂ = 2(θ+1)/(θ-1)`, for `u ≤ 1`, `c₂ u ≤ 1/2`. -/
lemma lambdaTwo_ge (θ u : ℝ) (hθ : 1 < θ) (hu : 0 < u) (hu1 : u ≤ 1)
    (hc : 2 * (θ + 1) / (θ - 1) * u ≤ 1 / 2) :
    1 - 2 * (θ + 1) / (θ - 1) * u ≤ lambdaTwo θ u := by
  set t := 2 * (θ + 1) / (θ - 1) * u with ht
  have hq := quad_factor θ u (1 - t) hθ hu.le
  have hexp := Real.abs_exp_sub_one_sub_id_le (x := u) (by rw [abs_of_pos hu]; exact hu1)
  have he1 : Real.exp u - 1 ≤ 2 * u := by
    have := (abs_le.mp hexp).2; nlinarith
  have he2 : 1 ≤ Real.exp u := Real.one_le_exp hu.le
  have h1 := lambdaOne_gt_one θ u hθ hu.le
  have hθ1 : θ - 1 ≠ 0 := by linarith
  have htθ : t * (θ - 1) = 2 * (θ + 1) * u := by
    rw [ht]; field_simp
  have ht0 : 0 ≤ t := by
    rw [ht]; positivity
  -- q(1-t) ≥ 0
  have hq0 : 0 ≤ (1 - t) ^ 2 - Real.exp u * (θ + 1) * (1 - t) + θ := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr he2),
      mul_le_mul_of_nonneg_left he1 (by linarith : (0:ℝ) ≤ θ + 1), sq_nonneg t]
  rw [hq] at hq0
  have hlt : 1 - t - lambdaOne θ u < 0 := by linarith
  by_contra hc2
  push Not at hc2
  have : 0 < 1 - t - lambdaTwo θ u := by linarith
  nlinarith


/-- the auxiliary constants -/
noncomputable def c2 (θ : ℝ) : ℝ := 2 * (θ + 1) / (θ - 1)
noncomputable def Cr (θ : ℝ) : ℝ := 2 * (2 + c2 θ) / (θ - 1)
noncomputable def C0 (θ : ℝ) : ℝ := 16 * θ * ((θ - 1) ^ 2 + θ * (2 * θ * c2 θ)) / (θ - 1) ^ 4

lemma c2_pos (θ : ℝ) (hθ : 1 < θ) : 0 < c2 θ := by
  unfold c2; have : 0 < θ - 1 := by linarith
  positivity

lemma c2_ge_two (θ : ℝ) (hθ : 1 < θ) : 2 ≤ c2 θ := by
  unfold c2; have : 0 < θ - 1 := by linarith
  rw [le_div_iff₀ this]; linarith

lemma Cr_pos (θ : ℝ) (hθ : 1 < θ) : 0 < Cr θ := by
  unfold Cr; have := c2_pos θ hθ; have : 0 < θ - 1 := by linarith
  positivity

lemma C0_nonneg (θ : ℝ) (hθ : 1 < θ) : 0 ≤ C0 θ := by
  unfold C0; have := c2_pos θ hθ; have : 0 < θ - 1 := by linarith
  positivity

/-- The package of estimates for small `u`. -/
lemma pkg (θ u : ℝ) (hθ : 1 < θ) (hu : 0 < u) (hu1 : u ≤ 1)
    (hc : c2 θ * u ≤ 1 / 2) (hu2 : u ≤ (θ - 1) / 4) (hu3 : 2 * θ * c2 θ * u ≤ 1)
    (hu4 : Cr θ * u ≤ 1) :
    0 < aU θ u ∧ 0 < bU θ u ∧ cU θ u = aU θ u + bU θ u ∧ 1 ≤ betaU θ u ∧ betaU θ u ≤ 1 + 2 * c2 θ * u ∧
    0 < bU θ u / aU θ u ∧ bU θ u / aU θ u ≤ 1 ∧ u / (2 * θ) ≤ bU θ u / aU θ u ∧
    bU θ u / aU θ u ≤ Cr θ * u ∧ |bU θ u / aU θ u - nu θ * u| ≤ C0 θ * u ^ 2 := by
  have hθ1 : 0 < θ - 1 := by linarith
  have hc2 := c2_pos θ hθ
  have hc22 := c2_ge_two θ hθ
  have hc' : 2 * (θ + 1) / (θ - 1) * u ≤ 1 / 2 := hc
  have hl2 := lambdaTwo_ge θ u hθ hu hu1 hc'
  have hl2' : 1 - c2 θ * u ≤ lambdaTwo θ u := hl2
  have hl1 := lambdaTwo_lt_one θ u hθ hu
  have hl2pos : 1 / 2 ≤ lambdaTwo θ u := by linarith
  have hmul := lambda_mul θ u hθ hu.le
  have hexp := Real.abs_exp_sub_one_sub_id_le (x := u) (by rw [abs_of_pos hu]; exact hu1)
  have he1 : Real.exp u - 1 ≤ 2 * u := by
    have := (abs_le.mp hexp).2; nlinarith
  have he0 : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  -- β = 1/λ₂
  have hβ : betaU θ u = 1 / lambdaTwo θ u := by
    unfold betaU
    have hθ0 : θ ≠ 0 := by linarith
    have hl0 : lambdaTwo θ u ≠ 0 := by linarith
    field_simp
    linear_combination hmul
  have hβ1 : 1 ≤ betaU θ u := by
    rw [hβ, le_div_iff₀ (by linarith)]; linarith
  have hβ2 : betaU θ u ≤ 1 + 2 * c2 θ * u := by
    rw [hβ, div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hl2' (by positivity : (0:ℝ) ≤ 1 + 2 * c2 θ * u)]
  have hl1β : lambdaOne θ u = θ * betaU θ u := by
    unfold betaU; field_simp
  -- a
  have ha_def : aU θ u = θ * betaU θ u - Real.exp u := by unfold aU; rw [hl1β]
  have ha1 : (θ - 1) / 2 ≤ aU θ u := by
    rw [ha_def]; nlinarith
  have ha2 : aU θ u ≤ θ := by
    rw [ha_def]; nlinarith
  have ha3 : |θ - 1 - aU θ u| ≤ 2 * θ * c2 θ * u := by
    rw [abs_le, ha_def]; constructor <;> nlinarith
  have ha0 : 0 < aU θ u := by linarith
  -- b
  have hb1 : u ≤ bU θ u := by unfold bU; linarith
  have hb2 : bU θ u ≤ (2 + c2 θ) * u := by unfold bU; nlinarith
  have hb0 : 0 < bU θ u := by linarith
  -- c
  have hc_eq : cU θ u = aU θ u + bU θ u := by unfold cU aU bU; ring
  -- b a = θ (e² - 1)
  have hba : bU θ u * aU θ u = θ * (Real.exp u ^ 2 - 1) := by
    have hq := quad_factor θ u (Real.exp u) hθ hu.le
    unfold bU aU
    linear_combination hq
  refine ⟨ha0, hb0, hc_eq, hβ1, hβ2, div_pos hb0 ha0, ?_, ?_, ?_, ?_⟩
  · rw [div_le_one ha0]
    calc bU θ u ≤ (2 + c2 θ) * u := hb2
      _ = Cr θ * u * ((θ - 1) / 2) := by unfold Cr; field_simp; try ring
      _ ≤ 1 * ((θ - 1) / 2) := mul_le_mul_of_nonneg_right hu4 (by linarith)
      _ ≤ aU θ u := by linarith
  · rw [div_le_div_iff₀ (by positivity) ha0]
    nlinarith
  · rw [div_le_iff₀ ha0]
    calc bU θ u ≤ (2 + c2 θ) * u := hb2
      _ = Cr θ * u * ((θ - 1) / 2) := by unfold Cr; field_simp; try ring
      _ ≤ Cr θ * u * aU θ u := mul_le_mul_of_nonneg_left ha1 (mul_nonneg (Cr_pos θ hθ).le hu.le)
  · -- the key second-order estimate
    have hr_eq : bU θ u / aU θ u - nu θ * u
        = θ * ((Real.exp u ^ 2 - 1 - 2 * u) * (θ - 1) ^ 2
            + 2 * u * ((θ - 1) ^ 2 - aU θ u ^ 2)) / (aU θ u ^ 2 * (θ - 1) ^ 2) := by
      have hr2 : bU θ u / aU θ u = θ * (Real.exp u ^ 2 - 1) / aU θ u ^ 2 := by
        rw [eq_div_iff (pow_ne_zero 2 ha0.ne'), div_mul_eq_mul_div, div_eq_iff ha0.ne']
        linear_combination aU θ u * hba
      rw [hr2]
      unfold nu
      field_simp
      ring
    have hexp2 := Real.abs_exp_sub_one_sub_id_le (x := 2 * u)
      (by rw [abs_of_pos (by linarith)]; nlinarith)
    have he2 : Real.exp u ^ 2 = Real.exp (2 * u) := by
      rw [sq, ← Real.exp_add]; ring_nf
    have hden : 0 < aU θ u ^ 2 * (θ - 1) ^ 2 := mul_pos (pow_pos ha0 2) (pow_pos hθ1 2)
    rw [hr_eq, abs_div, abs_mul, abs_of_pos (by linarith : (0:ℝ) < θ), abs_of_pos hden,
      div_le_iff₀ hden]
    have hnum : |(Real.exp u ^ 2 - 1 - 2 * u) * (θ - 1) ^ 2
            + 2 * u * ((θ - 1) ^ 2 - aU θ u ^ 2)|
        ≤ 4 * u ^ 2 * (θ - 1) ^ 2 + 2 * u * (2 * θ * c2 θ * u * (2 * θ)) := by
      calc _ ≤ |(Real.exp u ^ 2 - 1 - 2 * u) * (θ - 1) ^ 2|
            + |2 * u * ((θ - 1) ^ 2 - aU θ u ^ 2)| := abs_add_le _ _
        _ = |Real.exp (2 * u) - 1 - 2 * u| * (θ - 1) ^ 2
            + 2 * u * (|θ - 1 - aU θ u| * (θ - 1 + aU θ u)) := by
            rw [abs_mul, abs_mul, he2, abs_of_pos (by positivity : (0:ℝ) < (θ - 1) ^ 2),
              abs_of_pos (by positivity : (0:ℝ) < 2 * u)]
            congr 2
            rw [show (θ - 1) ^ 2 - aU θ u ^ 2 = (θ - 1 - aU θ u) * (θ - 1 + aU θ u) by ring,
              abs_mul, abs_of_pos (by linarith : 0 < θ - 1 + aU θ u)]
        _ ≤ (2 * u) ^ 2 * (θ - 1) ^ 2 + 2 * u * (2 * θ * c2 θ * u * (2 * θ)) := by
            gcongr
            linarith
        _ = 4 * u ^ 2 * (θ - 1) ^ 2 + 2 * u * (2 * θ * c2 θ * u * (2 * θ)) := by ring
    have hA2 : (θ - 1) ^ 4 / 4 ≤ aU θ u ^ 2 * (θ - 1) ^ 2 := by
      have : ((θ - 1) / 2) ^ 2 ≤ aU θ u ^ 2 := by gcongr
      calc (θ - 1) ^ 4 / 4 = ((θ - 1) / 2) ^ 2 * (θ - 1) ^ 2 := by ring
        _ ≤ aU θ u ^ 2 * (θ - 1) ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
    have hC0 : C0 θ * u ^ 2 * ((θ - 1) ^ 4 / 4) ≤ C0 θ * u ^ 2 * (aU θ u ^ 2 * (θ - 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hA2 (mul_nonneg (C0_nonneg θ hθ) (sq_nonneg u))
    have hC0' : C0 θ * u ^ 2 * ((θ - 1) ^ 4 / 4)
        = θ * (4 * u ^ 2 * (θ - 1) ^ 2 + 2 * u * (2 * θ * c2 θ * u * (2 * θ))) := by
      unfold C0; field_simp; ring
    calc θ * |(Real.exp u ^ 2 - 1 - 2 * u) * (θ - 1) ^ 2 + 2 * u * ((θ - 1) ^ 2 - aU θ u ^ 2)|
        ≤ θ * (4 * u ^ 2 * (θ - 1) ^ 2 + 2 * u * (2 * θ * c2 θ * u * (2 * θ))) := by
          apply mul_le_mul_of_nonneg_left hnum; linarith
      _ = C0 θ * u ^ 2 * ((θ - 1) ^ 4 / 4) := hC0'.symm
      _ ≤ C0 θ * u ^ 2 * (aU θ u ^ 2 * (θ - 1) ^ 2) := hC0

/-- Case A of the termwise bound: `y` close to 1. -/
lemma termA (u r ν c₂ C₀ Cr x y m : ℝ) (hu : 0 < u) (hν : 0 < ν) (hc₂ : 0 < c₂)
    (hC₀ : 0 ≤ C₀) (hCr : 0 < Cr) (hm : 1 ≤ m)
    (hr0 : 0 < r) (hru : r ≤ Cr * u) (hrν : |r - ν * u| ≤ C₀ * u ^ 2)
    (hx : 0 < x) (hy1 : 1 ≤ y) (hA : 2 * c₂ * u * m ≤ 1) (hyA : y ≤ 1 + 4 * c₂ * u * m) :
    |y * (1 + r) / (1 + r * x * y ^ 2) - 1 / (1 + ν * u * x)|
      ≤ (4 * c₂ + 3 * Cr + (C₀ + 16 * Cr * c₂) / ν) * m * u := by
  have hum : 0 < u * m := by positivity
  have hy3 : y ≤ 3 := by nlinarith
  have hD1 : 1 ≤ 1 + r * x * y ^ 2 := by nlinarith [mul_pos (mul_pos hr0 hx) (by positivity : 0 < y ^ 2)]
  have hD2 : 1 ≤ 1 + ν * u * x := by nlinarith [mul_pos (mul_pos hν hu) hx]
  have hD1p : 0 < 1 + r * x * y ^ 2 := by linarith
  have hD2p : 0 < 1 + ν * u * x := by linarith
  have hsplit : y * (1 + r) / (1 + r * x * y ^ 2) - 1 / (1 + ν * u * x)
      = (y * (1 + r) - 1) / (1 + r * x * y ^ 2)
        + (1 / (1 + r * x * y ^ 2) - 1 / (1 + ν * u * x)) := by ring
  rw [hsplit]
  -- first piece
  have h1a : 0 ≤ y * (1 + r) - 1 := by nlinarith
  have h1 : |(y * (1 + r) - 1) / (1 + r * x * y ^ 2)| ≤ 4 * c₂ * u * m + 3 * Cr * u := by
    rw [abs_of_nonneg (div_nonneg h1a hD1p.le)]
    calc (y * (1 + r) - 1) / (1 + r * x * y ^ 2) ≤ y * (1 + r) - 1 := div_le_self h1a hD1
      _ = (y - 1) + y * r := by ring
      _ ≤ 4 * c₂ * u * m + 3 * Cr * u := by nlinarith
  -- second piece
  have h2 : |1 / (1 + r * x * y ^ 2) - 1 / (1 + ν * u * x)|
      ≤ (C₀ * u + 16 * Cr * c₂ * u * m) / ν := by
    have heq : 1 / (1 + r * x * y ^ 2) - 1 / (1 + ν * u * x)
        = x * (ν * u - r * y ^ 2) / ((1 + r * x * y ^ 2) * (1 + ν * u * x)) := by
      field_simp
      ring
    rw [heq, abs_div, abs_mul, abs_of_pos hx, abs_of_pos (mul_pos hD1p hD2p)]
    have hnum : |ν * u - r * y ^ 2| ≤ C₀ * u ^ 2 + 16 * Cr * c₂ * u ^ 2 * m := by
      have : ν * u - r * y ^ 2 = (ν * u - r) - r * (y ^ 2 - 1) := by ring
      rw [this]
      have hy2 : y ^ 2 - 1 ≤ 16 * c₂ * u * m := by
        have e1 : y ^ 2 - 1 = (y - 1) * (y + 1) := by ring
        rw [e1]
        calc (y - 1) * (y + 1) ≤ (4 * c₂ * u * m) * 4 :=
              mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
          _ = 16 * c₂ * u * m := by ring
      have hy2' : 0 ≤ y ^ 2 - 1 := by nlinarith
      calc |(ν * u - r) - r * (y ^ 2 - 1)| ≤ |ν * u - r| + |r * (y ^ 2 - 1)| := abs_sub _ _
        _ = |r - ν * u| + r * (y ^ 2 - 1) := by
            rw [abs_sub_comm, abs_of_nonneg (mul_nonneg hr0.le hy2')]
        _ ≤ C₀ * u ^ 2 + Cr * u * (16 * c₂ * u * m) :=
            add_le_add hrν (mul_le_mul hru hy2 hy2' (by positivity))
        _ = C₀ * u ^ 2 + 16 * Cr * c₂ * u ^ 2 * m := by ring
    rw [div_le_div_iff₀ (mul_pos hD1p hD2p) hν]
    have hx' : x * ν * u ≤ 1 + ν * u * x := by nlinarith
    have hE : 0 ≤ C₀ * u + 16 * Cr * c₂ * u * m := by positivity
    calc x * |ν * u - r * y ^ 2| * ν ≤ x * (C₀ * u ^ 2 + 16 * Cr * c₂ * u ^ 2 * m) * ν :=
          by gcongr
      _ = (x * ν * u) * (C₀ * u + 16 * Cr * c₂ * u * m) := by ring
      _ ≤ (1 + ν * u * x) * (C₀ * u + 16 * Cr * c₂ * u * m) :=
          mul_le_mul_of_nonneg_right hx' hE
      _ = (C₀ * u + 16 * Cr * c₂ * u * m) * (1 * (1 + ν * u * x)) := by ring
      _ ≤ (C₀ * u + 16 * Cr * c₂ * u * m) * ((1 + r * x * y ^ 2) * (1 + ν * u * x)) := by
          apply mul_le_mul_of_nonneg_left _ hE
          exact mul_le_mul_of_nonneg_right hD1 hD2p.le
  calc |(y * (1 + r) - 1) / (1 + r * x * y ^ 2) + (1 / (1 + r * x * y ^ 2) - 1 / (1 + ν * u * x))|
      ≤ |(y * (1 + r) - 1) / (1 + r * x * y ^ 2)| + |1 / (1 + r * x * y ^ 2) - 1 / (1 + ν * u * x)| :=
        abs_add_le _ _
    _ ≤ (4 * c₂ * u * m + 3 * Cr * u) + (C₀ * u + 16 * Cr * c₂ * u * m) / ν := add_le_add h1 h2
    _ = (4 * c₂ * m + 3 * Cr + (C₀ + 16 * Cr * c₂ * m) / ν) * u := by field_simp; try ring
    _ ≤ (4 * c₂ + 3 * Cr + (C₀ + 16 * Cr * c₂) / ν) * m * u := by
        have : (4 * c₂ * m + 3 * Cr + (C₀ + 16 * Cr * c₂ * m) / ν)
            ≤ (4 * c₂ + 3 * Cr + (C₀ + 16 * Cr * c₂) / ν) * m := by
          have key : (4 * c₂ + 3 * Cr + (C₀ + 16 * Cr * c₂) / ν) * m
              - (4 * c₂ * m + 3 * Cr + (C₀ + 16 * Cr * c₂ * m) / ν)
              = 3 * Cr * (m - 1) + C₀ * (m - 1) / ν := by field_simp; ring
          have hm1 : 0 ≤ m - 1 := by linarith
          have : 0 ≤ 3 * Cr * (m - 1) + C₀ * (m - 1) / ν := by positivity
          linarith
        exact mul_le_mul_of_nonneg_right this hu.le

/-- Case B of the termwise bound: `y` far from 1. -/
lemma termB (θ u r ν c₂ x y m : ℝ) (hθ : 1 < θ) (hu : 0 < u) (hν : 0 < ν) (hc₂ : 0 < c₂)
    (hm : 1 ≤ m) (hr0 : 0 < r) (hr1 : r ≤ 1) (hrl : u / (2 * θ) ≤ r)
    (hx : 0 < x) (hxm : m * (θ - 1) ≤ x) (hy1 : 1 ≤ y) (hB : 1 < 2 * c₂ * u * m) :
    |y * (1 + r) / (1 + r * x * y ^ 2) - 1 / (1 + ν * u * x)|
      ≤ (2 * c₂ * (1 + 8 * θ * c₂ / (θ - 1))) * m * u := by
  have hD1p : 0 < 1 + r * x * y ^ 2 := by
    nlinarith [mul_pos (mul_pos hr0 hx) (by positivity : 0 < y ^ 2)]
  have hD2p : 0 < 1 + ν * u * x := by nlinarith [mul_pos (mul_pos hν hu) hx]
  have hrx : 0 < r * x := mul_pos hr0 hx
  have hθ1 : 0 < θ - 1 := by linarith
  have hp1 : y * (1 + r) / (1 + r * x * y ^ 2) ≤ 2 / (r * x) := by
    rw [div_le_div_iff₀ hD1p hrx]
    nlinarith [mul_pos hrx (by positivity : 0 < y), mul_nonneg hrx.le (by nlinarith : 0 ≤ y ^ 2 - y),
      mul_nonneg (mul_nonneg hrx.le (by nlinarith : 0 ≤ y ^ 2 - y)) (by linarith : 0 ≤ 1 - r)]
  have hp2 : 2 / (r * x) ≤ 8 * θ * c₂ / (θ - 1) := by
    rw [div_le_div_iff₀ hrx hθ1]
    have h1 : u / (2 * θ) * (m * (θ - 1)) ≤ r * x :=
      mul_le_mul hrl hxm (by positivity) hr0.le
    have h2 : u / (2 * θ) * (m * (θ - 1)) = u * m * (θ - 1) / (2 * θ) := by ring
    rw [h2] at h1
    have h3 : u * m * (θ - 1) / (2 * θ) * (8 * θ * c₂) = 4 * c₂ * u * m * (θ - 1) := by
      field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 8 * θ * c₂),
      mul_lt_mul_of_pos_right hB hθ1]
  have hp3 : 1 / (1 + ν * u * x) ≤ 1 := by
    rw [div_le_one hD2p]; nlinarith [mul_pos (mul_pos hν hu) hx]
  calc |y * (1 + r) / (1 + r * x * y ^ 2) - 1 / (1 + ν * u * x)|
      ≤ |y * (1 + r) / (1 + r * x * y ^ 2)| + |1 / (1 + ν * u * x)| := abs_sub _ _
    _ = y * (1 + r) / (1 + r * x * y ^ 2) + 1 / (1 + ν * u * x) := by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    _ ≤ 8 * θ * c₂ / (θ - 1) + 1 := by linarith
    _ = (1 + 8 * θ * c₂ / (θ - 1)) * 1 := by ring
    _ ≤ (1 + 8 * θ * c₂ / (θ - 1)) * (2 * c₂ * u * m) := by
        apply mul_le_mul_of_nonneg_left hB.le; positivity
    _ = (2 * c₂ * (1 + 8 * θ * c₂ / (θ - 1))) * m * u := by ring

/-- the global constant of the termwise bound -/
noncomputable def CT (θ : ℝ) : ℝ :=
  (4 * c2 θ + 3 * Cr θ + (C0 θ + 16 * Cr θ * c2 θ) / nu θ) + 2 * c2 θ * (1 + 8 * θ * c2 θ / (θ - 1))

lemma nu_pos (θ : ℝ) (hθ : 1 < θ) : 0 < nu θ := by
  unfold nu; have : 0 < θ - 1 := by linarith
  positivity

lemma CT_nonneg (θ : ℝ) (hθ : 1 < θ) : 0 ≤ CT θ := by
  unfold CT
  have := c2_pos θ hθ; have := Cr_pos θ hθ; have := C0_nonneg θ hθ; have := nu_pos θ hθ
  have : 0 < θ - 1 := by linarith
  positivity

/-- the termwise bound, for `y = β^m`, `x = θ^m`. -/
lemma term_bound (θ u : ℝ) (hθ : 1 < θ) (hu : 0 < u) (hu1 : u ≤ 1)
    (hc : c2 θ * u ≤ 1 / 2) (hu2 : u ≤ (θ - 1) / 4) (hu3 : 2 * θ * c2 θ * u ≤ 1)
    (hu4 : Cr θ * u ≤ 1) (m : ℕ) (hm : 1 ≤ m) :
    |betaU θ u ^ m * (1 + bU θ u / aU θ u) /
        (1 + bU θ u / aU θ u * θ ^ m * (betaU θ u ^ m) ^ 2) - 1 / (1 + nu θ * u * θ ^ m)|
      ≤ CT θ * m * u := by
  obtain ⟨ha0, hb0, hc_eq, hβ1, hβ2, hr0, hr1, hrl, hru, hrν⟩ :=
    pkg θ u hθ hu hu1 hc hu2 hu3 hu4
  have hc2 := c2_pos θ hθ
  have hCr := Cr_pos θ hθ
  have hC0 := C0_nonneg θ hθ
  have hν := nu_pos θ hθ
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hx : 0 < θ ^ m := by positivity
  have hxm : (m:ℝ) * (θ - 1) ≤ θ ^ m := by
    have := one_add_mul_le_pow (by linarith : (-2:ℝ) ≤ θ - 1) m
    rw [show (1:ℝ) + (θ - 1) = θ by ring] at this
    linarith
  have hy1 : 1 ≤ betaU θ u ^ m := one_le_pow₀ hβ1
  have hθ1 : 0 < θ - 1 := by linarith
  have hCTa : 0 ≤ 2 * c2 θ * (1 + 8 * θ * c2 θ / (θ - 1)) := by positivity
  have hCTb : 0 ≤ 4 * c2 θ + 3 * Cr θ + (C0 θ + 16 * Cr θ * c2 θ) / nu θ := by positivity
  by_cases hA : 2 * c2 θ * u * m ≤ 1
  · have hyA : betaU θ u ^ m ≤ 1 + 4 * c2 θ * u * m := by
      have h1 : betaU θ u ^ m ≤ (1 + 2 * c2 θ * u) ^ m :=
        pow_le_pow_left₀ (by linarith) hβ2 m
      have h2 : (1 + 2 * c2 θ * u) ^ m ≤ Real.exp (2 * c2 θ * u) ^ m := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [Real.add_one_le_exp (2 * c2 θ * u)]
      have h3 : Real.exp (2 * c2 θ * u) ^ m = Real.exp (m * (2 * c2 θ * u)) :=
        (Real.exp_nat_mul _ _).symm
      have h4 := Real.abs_exp_sub_one_sub_id_le (x := m * (2 * c2 θ * u))
        (by rw [abs_of_nonneg (by positivity)]; linarith)
      have h5 := (abs_le.mp h4).2
      have h6 : (m * (2 * c2 θ * u)) ^ 2 ≤ m * (2 * c2 θ * u) := by
        have : 0 ≤ m * (2 * c2 θ * u) := by positivity
        nlinarith
      calc betaU θ u ^ m ≤ Real.exp (m * (2 * c2 θ * u)) := by rw [← h3]; exact h1.trans h2
        _ ≤ 1 + m * (2 * c2 θ * u) + (m * (2 * c2 θ * u)) ^ 2 := by linarith
        _ ≤ 1 + 4 * c2 θ * u * m := by linarith
    have := termA u (bU θ u / aU θ u) (nu θ) (c2 θ) (C0 θ) (Cr θ) (θ ^ m) (betaU θ u ^ m) m
      hu hν hc2 hC0 hCr hm' hr0 hru hrν hx hy1 hA hyA
    calc _ ≤ _ := this
      _ ≤ CT θ * m * u := by
        unfold CT
        apply mul_le_mul_of_nonneg_right _ hu.le
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        linarith
  · push Not at hA
    have := termB θ u (bU θ u / aU θ u) (nu θ) (c2 θ) (θ ^ m) (betaU θ u ^ m) m
      hθ hu hν hc2 hm' hr0 hr1 hrl hx hxm hy1 hA
    calc _ ≤ _ := this
      _ ≤ CT θ * m * u := by
        unfold CT
        apply mul_le_mul_of_nonneg_right _ hu.le
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        linarith

/-- the main per-`u` bound -/
lemma main_bound (γ θ u : ℝ) (hθ : 1 < θ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (hc : c2 θ * u ≤ 1 / 2) (hu2 : u ≤ (θ - 1) / 4) (hu3 : 2 * θ * c2 θ * u ≤ 1)
    (hu4 : Cr θ * u ≤ 1) :
    |phiSeries γ θ u - psi γ θ u|
      ≤ (1 - γ) / γ * (CT θ * (∑' j : ℕ, ((j : ℝ) + 1) * γ ^ (j + 1))) * u := by
  obtain ⟨ha0, hb0, hc_eq, hβ1, hβ2, hr0, hr1, hrl, hru, hrν⟩ :=
    pkg θ u hθ hu hu1 hc hu2 hu3 hu4
  have hCT := CT_nonneg θ hθ
  have hν := nu_pos θ hθ
  set f : ℕ → ℝ := fun j => cU θ u * (γ * betaU θ u) ^ (j + 1) /
      (aU θ u + bU θ u * (θ * (betaU θ u) ^ 2) ^ (j + 1)) with hf
  set g : ℕ → ℝ := fun j => γ ^ (j + 1) / (1 + nu θ * u * θ ^ (j + 1)) with hg
  have hphi : phiSeries γ θ u = (1 - γ) / γ * ∑' j, f j := rfl
  have hpsi : psi γ θ u = (1 - γ) / γ * ∑' j, g j := rfl
  -- termwise identity
  have hfg : ∀ j, f j - g j = γ ^ (j + 1) *
      (betaU θ u ^ (j + 1) * (1 + bU θ u / aU θ u) /
        (1 + bU θ u / aU θ u * θ ^ (j + 1) * (betaU θ u ^ (j + 1)) ^ 2)
        - 1 / (1 + nu θ * u * θ ^ (j + 1))) := by
    intro j
    simp only [hf, hg]
    rw [hc_eq, mul_pow, mul_pow, ← pow_mul, mul_comm 2 (j + 1), pow_mul]
    have hden : 0 < aU θ u + bU θ u * (θ ^ (j + 1) * (betaU θ u ^ (j + 1)) ^ 2) := by
      positivity
    have hden2 : 0 < 1 + bU θ u / aU θ u * θ ^ (j + 1) * (betaU θ u ^ (j + 1)) ^ 2 := by
      positivity
    field_simp
    try ring
  -- termwise bound
  have hT : ∀ j : ℕ, |f j - g j| ≤ CT θ * ((j : ℝ) + 1) * u * γ ^ (j + 1) := by
    intro j
    rw [hfg, abs_mul, abs_of_pos (by positivity : (0:ℝ) < γ ^ (j + 1))]
    have := term_bound θ u hθ hu hu1 hc hu2 hu3 hu4 (j + 1) (by omega)
    push_cast at this
    calc γ ^ (j + 1) * _ ≤ γ ^ (j + 1) * (CT θ * ((j : ℝ) + 1) * u) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = CT θ * ((j : ℝ) + 1) * u * γ ^ (j + 1) := by ring
  -- summability
  have hS : Summable (fun j : ℕ => ((j : ℝ) + 1) * γ ^ (j + 1)) := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1
      (r := γ) (by rw [Real.norm_eq_abs, abs_of_pos hγ0]; exact hγ1)
    have h2 := summable_geometric_of_lt_one hγ0.le hγ1
    have h3 := (h1.add h2).mul_left γ
    refine h3.congr fun j => ?_
    simp only [pow_one]; ring
  have hgs : Summable g := by
    refine Summable.of_norm_bounded (g := fun j => γ ^ (j + 1))
      ((summable_geometric_of_lt_one hγ0.le hγ1).mul_left γ |>.congr fun j => by ring) ?_
    intro j
    simp only [hg, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    apply div_le_self (by positivity)
    nlinarith [mul_pos (mul_pos hν hu) (pow_pos (by linarith : (0:ℝ) < θ) (j + 1))]
  have hds : Summable (fun j => f j - g j) := by
    refine Summable.of_norm_bounded (g := fun j => CT θ * ((j : ℝ) + 1) * u * γ ^ (j + 1))
      ((hS.mul_left (CT θ * u)).congr fun j => by ring) ?_
    intro j; rw [Real.norm_eq_abs]; exact hT j
  have hfs : Summable f := by
    have := hds.add hgs
    refine this.congr fun j => ?_
    exact sub_add_cancel _ _
  have hmaj : Summable (fun j : ℕ => CT θ * ((j : ℝ) + 1) * u * γ ^ (j + 1)) :=
    (hS.mul_left (CT θ * u)).congr fun j => by ring
  have hns : Summable (fun j => ‖f j - g j‖) :=
    Summable.of_nonneg_of_le (f := fun j : ℕ => CT θ * ((j : ℝ) + 1) * u * γ ^ (j + 1))
      (fun j => norm_nonneg _) (fun j => by rw [Real.norm_eq_abs]; exact hT j) hmaj
  -- assemble
  rw [hphi, hpsi, ← mul_sub, ← hfs.tsum_sub hgs, abs_mul,
    abs_of_nonneg (by apply div_nonneg <;> linarith : (0:ℝ) ≤ (1 - γ) / γ)]
  have hbound : |∑' j, (f j - g j)| ≤ CT θ * (∑' j : ℕ, ((j : ℝ) + 1) * γ ^ (j + 1)) * u := by
    calc |∑' j, (f j - g j)| = ‖∑' j, (f j - g j)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' j, ‖f j - g j‖ := norm_tsum_le_tsum_norm hns
      _ ≤ ∑' j : ℕ, CT θ * ((j : ℝ) + 1) * u * γ ^ (j + 1) := by
          apply hns.tsum_le_tsum _ hmaj
          intro j; rw [Real.norm_eq_abs]; exact hT j
      _ = ∑' j : ℕ, (CT θ * u) * (((j : ℝ) + 1) * γ ^ (j + 1)) := by
          congr 1; ext j; ring
      _ = (CT θ * u) * ∑' j : ℕ, ((j : ℝ) + 1) * γ ^ (j + 1) := tsum_mul_left
      _ = CT θ * (∑' j : ℕ, ((j : ℝ) + 1) * γ ^ (j + 1)) * u := by ring
  calc (1 - γ) / γ * |∑' j, (f j - g j)|
      ≤ (1 - γ) / γ * (CT θ * (∑' j : ℕ, ((j : ℝ) + 1) * γ ^ (j + 1)) * u) :=
        mul_le_mul_of_nonneg_left hbound (by apply div_nonneg <;> linarith)
    _ = _ := by ring

theorem lemma_2_6_core (γ θ : ℝ) (hθ : 1 < θ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hcritical : 1 ≤ γ * θ) :
    (fun u => phiSeries γ θ u - psi γ θ u) =O[𝓝[>] (0 : ℝ)] (fun u => u) := by
  have hc2 := c2_pos θ hθ
  have hCr := Cr_pos θ hθ
  have hθ1 : 0 < θ - 1 := by linarith
  apply Asymptotics.IsBigO.of_bound
    ((1 - γ) / γ * (CT θ * (∑' j : ℕ, ((j : ℝ) + 1) * γ ^ (j + 1))))
  have h1 : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT one_pos
  have h2 : Set.Ioo (0:ℝ) (1 / (2 * c2 θ)) ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (by positivity)
  have h3 : Set.Ioo (0:ℝ) ((θ - 1) / 4) ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (by positivity)
  have h4 : Set.Ioo (0:ℝ) (1 / (2 * θ * c2 θ)) ∈ 𝓝[>] (0:ℝ) :=
    Ioo_mem_nhdsGT (by have : 0 < θ := by linarith
                       positivity)
  have h5 : Set.Ioo (0:ℝ) (1 / Cr θ) ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (by positivity)
  filter_upwards [h1, h2, h3, h4, h5] with u hu1 hu2 hu3 hu4 hu5
  have hu : 0 < u := hu1.1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hu]
  apply main_bound γ θ u hθ hγ0 hγ1 hu hu1.2.le
  · have := hu2.2; rw [lt_div_iff₀ (by positivity)] at this; linarith
  · exact hu3.2.le
  · have := hu4.2
    rw [lt_div_iff₀ (by have : 0 < θ := by linarith
                        positivity)] at this
    linarith
  · have := hu5.2; rw [lt_div_iff₀ hCr] at this; linarith

end SolomonRWRE.SlowApproach

open SolomonRWRE.SlowApproach


theorem solution (γ θ : ℝ) (hθ : 1 < θ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hcritical : 1 ≤ γ * θ) :
    (fun u => phiSeries γ θ u - psi γ θ u) =O[𝓝[>] (0 : ℝ)] (fun u => u) := by
  exact lemma_2_6_core γ θ hθ hγ0 hγ1 hcritical
