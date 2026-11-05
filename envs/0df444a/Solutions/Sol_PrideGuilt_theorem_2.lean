-- Prove2me | solution 1 for PrideGuilt.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-11-04T14:49:55.180773+00:00
-- url     : https://prove2.me/submissions/84d6594f-8c2c-43da-a412-67f92e4fe400

import Definitions.Def_PrideGuilt_Standing
import Definitions.Def_PrideGuilt_optProfit
import Definitions.Def_PrideGuilt_InOmega4
import Definitions.Def_PrideGuilt_tauMStar

namespace PrideGuilt

/-- `N = b₀(x − (c_r − Δc)) − b₁ y`. -/
noncomputable def pgN (P : Params) (x y : ℝ) : ℝ := P.b0 * (x - (cr P - dc P)) - P.b1 * y

/-- `M = h₀ + N² / (4 b₀ (x − y))`, the optimal effective market size. -/
noncomputable def pgM (P : Params) (x y : ℝ) : ℝ :=
  (1 - P.b1 * P.IG - P.b0 * P.cn) + pgN P x y ^ 2 / (4 * P.b0 * (x - y))

/-- Closed form of the optimal profit on `Ω₄`. -/
noncomputable def pgF (P : Params) (x y : ℝ) : ℝ := pgM P x y ^ 2 / (4 * P.b0)

/-- The effective market size at reward `f`: `1 + b₁ Ū(f) − b₀ c(f)`. -/
noncomputable def pgH (P : Params) (x y f : ℝ) : ℝ :=
  1 + P.b1 * Ubar P x y f
    - P.b0 * (tauStar P x y f * (P.cu + f) + (1 - tauStar P x y f) * P.cn)

lemma pg_omega_poly (P : Params) (hb0 : 0 < P.b0) (x y : ℝ) (h : InOmega4 P x y) :
    0 < pgN P x y ∧ pgN P x y < 2 * P.b0 * (x - y) := by
  obtain ⟨h1, h2⟩ := h
  have e1 : P.b1 / P.b0 * P.b0 = P.b1 := div_mul_cancel₀ _ hb0.ne'
  have e2 : P.b1 * y / P.b0 * P.b0 = P.b1 * y := div_mul_cancel₀ _ hb0.ne'
  have k1 := mul_lt_mul_of_pos_right h1 hb0
  have k2 := mul_lt_mul_of_pos_right h2 hb0
  unfold pgN
  constructor
  · have : (x - P.b1 * y / P.b0) * P.b0 = x * P.b0 - P.b1 * y := by rw [sub_mul, e2]
    nlinarith
  · have : ((2 - P.b1 / P.b0) * y - x) * P.b0 = 2 * y * P.b0 - P.b1 * y - x * P.b0 := by
      have : ((2 - P.b1 / P.b0) * y - x) * P.b0 = 2 * y * P.b0 - (P.b1 / P.b0 * P.b0) * y
        - x * P.b0 := by ring
      rw [this, e1]
    nlinarith

lemma pg_lt (P : Params) (hb0 : 0 < P.b0) (x y : ℝ) (h : InOmega4 P x y) : y < x := by
  obtain ⟨h1, h2⟩ := pg_omega_poly P hb0 x y h
  nlinarith

lemma pg_profit_eq (P : Params) (x y p f : ℝ) :
    P.b0 * profit P x y p f = demand P x y p f * (pgH P x y f - demand P x y p f) := by
  unfold profit demand unitProfit pgH; ring

lemma pg_H_le (P : Params) (hP : Standing P) (x y : ℝ) (h : InOmega4 P x y) (f : ℝ) :
    pgH P x y f ≤ pgM P x y := by
  have hb0 := hP.b0_pos
  have hxy := pg_lt P hb0 x y h
  have hΔ : 0 < x - y := by linarith
  have hD : 0 < 4 * P.b0 * (x - y) := by positivity
  unfold pgH Ubar tauStar
  rw [max_eq_left hxy.le, min_eq_right hxy.le]
  split_ifs with c1 c2
  · unfold UN pgM
    have : 0 ≤ pgN P x y ^ 2 / (4 * P.b0 * (x - y)) := by positivity
    nlinarith
  · unfold UR pgM
    have key : pgN P x y ^ 2 / (4 * P.b0 * (x - y)) =
        pgN P x y - P.b0 * (x - y) + (pgN P x y - 2 * P.b0 * (x - y)) ^ 2 / (4 * P.b0 * (x - y)) := by
      field_simp; ring
    have : 0 ≤ (pgN P x y - 2 * P.b0 * (x - y)) ^ 2 / (4 * P.b0 * (x - y)) := by positivity
    have hb := hP.b1_le_b0
    have : (P.b1 - P.b0) * (f - (cr P - y)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    rw [key]; unfold pgN cr dc at *; nlinarith
  · unfold UR pgM
    set τ := tauM P x y f with hτ
    have hf : f = cr P - x + τ * (x - y) := by
      rw [hτ]; unfold tauM; field_simp; ring
    have key : pgN P x y ^ 2 / (4 * P.b0 * (x - y)) =
        τ * pgN P x y - P.b0 * (x - y) * τ ^ 2
          + (pgN P x y - 2 * P.b0 * (x - y) * τ) ^ 2 / (4 * P.b0 * (x - y)) := by
      field_simp; ring
    have : 0 ≤ (pgN P x y - 2 * P.b0 * (x - y) * τ) ^ 2 / (4 * P.b0 * (x - y)) := by positivity
    rw [key]
    have e : 1 + P.b1 * (f - P.ce + P.IP + (1 - τ) * x) - P.b0 * (τ * (P.cu + f) + (1 - τ) * P.cn)
        = 1 - P.b1 * P.IG - P.b0 * P.cn + (τ * pgN P x y - P.b0 * (x - y) * τ ^ 2) := by
      rw [hf]; unfold pgN cr dc; ring
    rw [e]; linarith

lemma pg_optProfit_eq (P : Params) (hP : Standing P) (x y : ℝ) (h : InOmega4 P x y) :
    optProfit P x y = pgF P x y := by
  have hb0 := hP.b0_pos
  have hxy := pg_lt P hb0 x y h
  have hΔ : 0 < x - y := by linarith
  obtain ⟨hN1, hN2⟩ := pg_omega_poly P hb0 x y h
  have hM : 0 ≤ pgM P x y := by
    unfold pgM; have := hP.market; have : 0 ≤ pgN P x y ^ 2 / (4 * P.b0 * (x - y)) := by positivity
    linarith
  unfold optProfit
  apply IsGreatest.csSup_eq
  constructor
  · -- attainment
    set τ := pgN P x y / (2 * P.b0 * (x - y)) with hτ
    have hτ0 : 0 < τ := by positivity
    have hτ1 : τ < 1 := by rw [hτ, div_lt_one (by positivity)]; exact hN2
    set f := cr P - x + τ * (x - y) with hf
    have hc1 : ¬ f ≤ cr P - max x y := by
      rw [max_eq_left hxy.le]; have := mul_pos hτ0 hΔ; linarith
    have hc2 : ¬ cr P - min x y ≤ f := by
      rw [min_eq_right hxy.le]; have := mul_lt_mul_of_pos_right hτ1 hΔ; linarith
    have htm : tauM P x y f = τ := by
      unfold tauM; rw [hf]; field_simp; ring
    have hU : Ubar P x y f = UR P x f τ := by
      unfold Ubar; rw [if_neg hc1, if_neg hc2, if_pos hxy, htm]
    have hT : tauStar P x y f = τ := by
      unfold tauStar; rw [if_neg hc1, if_neg hc2, if_pos hxy, htm]
    have hH : pgH P x y f = pgM P x y := by
      unfold pgH pgM; rw [hU, hT]; unfold UR
      rw [hf, hτ]; unfold pgN cr dc; field_simp; ring
    refine ⟨(1 + P.b1 * Ubar P x y f - pgM P x y / 2) / P.b0, f, ?_, ?_⟩
    · unfold demand; field_simp; linarith
    · have h1 := pg_profit_eq P x y ((1 + P.b1 * Ubar P x y f - pgM P x y / 2) / P.b0) f
      have h2 : demand P x y ((1 + P.b1 * Ubar P x y f - pgM P x y / 2) / P.b0) f
          = pgM P x y / 2 := by unfold demand; field_simp; ring
      rw [h2, hH] at h1
      unfold pgF; rw [div_eq_iff (by positivity)]; linear_combination (-4) * h1
  · rintro π ⟨p, f, hd, rfl⟩
    have h1 := pg_profit_eq P x y p f
    have h2 := pg_H_le P hP x y h f
    unfold pgF
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h2 hd, sq_nonneg (pgM P x y - 2 * demand P x y p f)]

lemma pg_hasDerivAt_x (P : Params) (hb0 : 0 < P.b0) (x y : ℝ) (hxy : y < x) :
    HasDerivAt (fun t => pgF P t y)
      (pgM P x y * (pgN P x y * (2 * P.b0 * (x - y) - pgN P x y)) / (8 * P.b0 ^ 2 * (x - y) ^ 2)) x := by
  have hΔ : x - y ≠ 0 := by linarith
  have hb : P.b0 ≠ 0 := hb0.ne'
  have hN : HasDerivAt (fun t => pgN P t y) P.b0 x := by
    have := (((hasDerivAt_id x).sub_const (cr P - dc P)).const_mul P.b0).sub_const (P.b1 * y)
    unfold pgN; exact this.congr_deriv (by ring)
  have hden : HasDerivAt (fun t => 4 * P.b0 * (t - y)) (4 * P.b0) x := by
    have := ((hasDerivAt_id x).sub_const y).const_mul (4 * P.b0)
    exact this.congr_deriv (by ring)
  have hq := ((hN.pow 2).div hden (by positivity)).const_add (1 - P.b1 * P.IG - P.b0 * P.cn)
  have hF := (hq.pow 2).div_const (4 * P.b0)
  unfold pgF pgM
  refine hF.congr_deriv ?_
  have h4 : 4 * P.b0 * (x - y) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hb) hΔ
  simp only [Pi.pow_apply, Pi.div_apply]
  generalize pgN P x y = N at *
  simp only [Nat.cast_ofNat, show (2:ℕ) - 1 = 1 from rfl, pow_one]
  field_simp
  ring

lemma pg_hasDerivAt_y (P : Params) (hb0 : 0 < P.b0) (x y : ℝ) (hxy : y < x) :
    HasDerivAt (fun t => pgF P x t)
      (pgM P x y * (pgN P x y * (pgN P x y - 2 * P.b1 * (x - y))) / (8 * P.b0 ^ 2 * (x - y) ^ 2)) y := by
  have hΔ : x - y ≠ 0 := by linarith
  have hb : P.b0 ≠ 0 := hb0.ne'
  have hN : HasDerivAt (fun t => pgN P x t) (-P.b1) y := by
    have := ((hasDerivAt_id y).const_mul P.b1).const_sub (P.b0 * (x - (cr P - dc P)))
    unfold pgN; exact this.congr_deriv (by ring)
  have hden : HasDerivAt (fun t => 4 * P.b0 * (x - t)) (-(4 * P.b0)) y := by
    have := ((hasDerivAt_id y).const_sub x).const_mul (4 * P.b0)
    exact this.congr_deriv (by ring)
  have hq := ((hN.pow 2).div hden (by positivity)).const_add (1 - P.b1 * P.IG - P.b0 * P.cn)
  have hF := (hq.pow 2).div_const (4 * P.b0)
  unfold pgF pgM
  refine hF.congr_deriv ?_
  have h4 : 4 * P.b0 * (x - y) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hb) hΔ
  simp only [Pi.pow_apply, Pi.div_apply]
  generalize pgN P x y = N at *
  simp only [Nat.cast_ofNat, show (2:ℕ) - 1 = 1 from rfl, pow_one]
  field_simp
  ring

theorem theorem_2 (P : Params) (hP : Standing P) (γP γG : ℝ) (hγP : 0 < γP) (hγG : 0 < γG)
    (hΩ : InOmega4 P γP γG) :
    DifferentiableAt ℝ (fun x => optProfit P x γG) γP ∧
    DifferentiableAt ℝ (fun y => optProfit P γP y) γG ∧
    0 ≤ deriv (fun x => optProfit P x γG) γP ∧
    ((P.b0 - 2 * P.b1) * γP + P.b1 * γG < P.b0 * (cr P - dc P) →
        deriv (fun y => optProfit P γP y) γG < 0) ∧
    (P.b0 * (cr P - dc P) ≤ (P.b0 - 2 * P.b1) * γP + P.b1 * γG →
        0 ≤ deriv (fun y => optProfit P γP y) γG) ∧
    ((P.b0 - 2 * P.b1) * γP + P.b1 * γG < P.b0 * (cr P - dc P) ↔
        tauMStar P γP γG < P.b1 / P.b0) ∧
    (P.b0 * γG - P.b1 * γP ≤ P.b0 * (cr P - dc P) →
        deriv (fun y => optProfit P γP y) γG ≤ deriv (fun x => optProfit P x γG) γP) ∧
    (P.b0 * (cr P - dc P) < P.b0 * γG - P.b1 * γP →
        deriv (fun x => optProfit P x γG) γP < deriv (fun y => optProfit P γP y) γG) ∧
    (P.b0 * γG - P.b1 * γP ≤ P.b0 * (cr P - dc P) ↔
        tauMStar P γP γG ≤ (P.b0 + P.b1) / (2 * P.b0)) := by
  have hb0 := hP.b0_pos
  have hb1 := hP.b1_nonneg
  have hxy := pg_lt P hb0 γP γG hΩ
  have hΔ : 0 < γP - γG := by linarith
  obtain ⟨hN1, hN2⟩ := pg_omega_poly P hb0 γP γG hΩ
  have hMpos : 0 < pgM P γP γG := by
    unfold pgM; have := hP.market
    have : 0 < pgN P γP γG ^ 2 / (4 * P.b0 * (γP - γG)) := by positivity
    linarith
  -- local agreement with the closed form
  have hopx : IsOpen {x : ℝ | InOmega4 P x γG} := by
    unfold InOmega4
    exact (isOpen_lt (continuous_const.sub continuous_id) continuous_const).inter
      (isOpen_lt continuous_const (continuous_id.sub continuous_const))
  have hopy : IsOpen {y : ℝ | InOmega4 P γP y} := by
    unfold InOmega4
    exact (isOpen_lt ((continuous_const.mul continuous_id).sub continuous_const) continuous_const).inter
      (isOpen_lt continuous_const (continuous_const.sub ((continuous_const.mul continuous_id).div_const _)))
  have hevx : (fun x => pgF P x γG) =ᶠ[nhds γP] (fun x => optProfit P x γG) :=
    Filter.eventually_of_mem (hopx.mem_nhds hΩ) (fun x hx => (pg_optProfit_eq P hP x γG hx).symm)
  have hevy : (fun y => pgF P γP y) =ᶠ[nhds γG] (fun y => optProfit P γP y) :=
    Filter.eventually_of_mem (hopy.mem_nhds hΩ) (fun y hy => (pg_optProfit_eq P hP γP y hy).symm)
  have hdx := (pg_hasDerivAt_x P hb0 γP γG hxy).congr_of_eventuallyEq hevx.symm
  have hdy := (pg_hasDerivAt_y P hb0 γP γG hxy).congr_of_eventuallyEq hevy.symm
  rw [hdx.deriv, hdy.deriv]
  set N := pgN P γP γG with hN
  set M := pgM P γP γG with hM
  set Δ := γP - γG with hΔdef
  have hK : 0 < 8 * P.b0 ^ 2 * Δ ^ 2 := by positivity
  have hτ : tauMStar P γP γG = N / (2 * P.b0 * Δ) := by
    unfold tauMStar; rw [hN]; unfold pgN; ring
  have c1 : (P.b0 - 2 * P.b1) * γP + P.b1 * γG < P.b0 * (cr P - dc P) ↔ N < 2 * P.b1 * Δ := by
    rw [hN, hΔdef]; unfold pgN; constructor <;> intro h <;> linarith
  have c2 : P.b0 * γG - P.b1 * γP ≤ P.b0 * (cr P - dc P) ↔ N ≤ (P.b0 + P.b1) * Δ := by
    rw [hN, hΔdef]; unfold pgN; constructor <;> intro h <;> linarith
  have hdiff : M * (N * (2 * P.b0 * Δ - N)) / (8 * P.b0 ^ 2 * Δ ^ 2)
      - M * (N * (N - 2 * P.b1 * Δ)) / (8 * P.b0 ^ 2 * Δ ^ 2)
      = 2 * (M * N) * ((P.b0 + P.b1) * Δ - N) / (8 * P.b0 ^ 2 * Δ ^ 2) := by ring
  have hMN : 0 < M * N := mul_pos hMpos hN1
  refine ⟨hdx.differentiableAt, hdy.differentiableAt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : 0 < 2 * P.b0 * Δ - N := by linarith
    positivity
  · intro h
    have h' := c1.mp h
    apply div_neg_of_neg_of_pos _ hK
    exact mul_neg_of_pos_of_neg hMpos (mul_neg_of_pos_of_neg hN1 (by linarith))
  · intro h
    have h' : 2 * P.b1 * Δ ≤ N := by
      by_contra hc; push Not at hc; exact absurd (c1.mpr hc) (not_lt.mpr h)
    apply div_nonneg _ hK.le
    exact mul_nonneg hMpos.le (mul_nonneg hN1.le (by linarith))
  · rw [c1, hτ, div_lt_div_iff₀ (by positivity) hb0]
    constructor <;> intro h <;> nlinarith
  · intro h
    have h' := c2.mp h
    have : 0 ≤ 2 * (M * N) * ((P.b0 + P.b1) * Δ - N) / (8 * P.b0 ^ 2 * Δ ^ 2) := by
      apply div_nonneg _ hK.le
      exact mul_nonneg (by positivity) (by linarith)
    linarith
  · intro h
    have h' : (P.b0 + P.b1) * Δ < N := by
      by_contra hc; push Not at hc; exact absurd (c2.mpr hc) (not_le.mpr h)
    have : 2 * (M * N) * ((P.b0 + P.b1) * Δ - N) / (8 * P.b0 ^ 2 * Δ ^ 2) < 0 := by
      apply div_neg_of_neg_of_pos _ hK
      exact mul_neg_of_pos_of_neg (by positivity) (by linarith)
    linarith
  · rw [c2, hτ, div_le_div_iff₀ (by positivity) (by positivity)]
    constructor <;> intro h <;> nlinarith

end PrideGuilt


-- Platform entry point: restates the target verbatim.
namespace PrideGuilt

/-- **Theorem 2 (impact of pride and guilt on the optimal profit in `Ω₄`), corrected: demand
`D ≥ 0` in (5).**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Theorem 2, p.18 (PDF 19).

Fix every parameter except `γ_P, γ_G`, assume the standing assumptions, `γ_P, γ_G > 0` and
`(γ_P, γ_G) ∈ Ω₄`, and write `d = c_r − Δc`. The optimal profit `Π*(γ_P, γ_G)` has partial
derivatives in `γ_P` and in `γ_G` at this point, and
(i) `∂Π*/∂γ_P ≥ 0`;
(ii) `∂Π*/∂γ_G < 0` if `(b₀ − 2b₁)γ_P + b₁γ_G < b₀d`, and `∂Π*/∂γ_G ≥ 0` if
  `(b₀ − 2b₁)γ_P + b₁γ_G ≥ b₀d`; the first condition holds iff `τ*_m < b₁/b₀`;
(iii) `∂Π*/∂γ_P ≥ ∂Π*/∂γ_G` if `b₀γ_G − b₁γ_P ≤ b₀d`, and `∂Π*/∂γ_P < ∂Π*/∂γ_G` if
  `b₀γ_G − b₁γ_P > b₀d`; the first condition holds iff `τ*_m ≤ (b₀ + b₁)/(2b₀)`.

**Formalization Note.** `Π*` is `optProfit`, the supremum of `Π(p, f)` over `(p, f) ∈ ℝ²` with
`D(p, f) ≥ 0` (correction; as printed, (5) is maximized at a negative demand and the theorem fails
at `b₀ = 1`, `b₁ = 0.5`, `c_n = 1`, `c_u = 0.5`, `c_e = 3`, `I_P = I_G = 0`, `γ_P = 4`, `γ_G = 1`).
The partial derivatives are `deriv` of the one-variable sections `x ↦ Π*(x, γ_G)` and
`y ↦ Π*(γ_P, y)`, whose differentiability is part of the conclusion. Each "i.e." equivalence is
one `↔`; its negation is the "i.e." of the second line. No `p* ≥ 0` restriction is assumed. -/
theorem _root_.solution (P : Params) (hP : Standing P) (γP γG : ℝ) (hγP : 0 < γP) (hγG : 0 < γG)
    (hΩ : InOmega4 P γP γG) :
    DifferentiableAt ℝ (fun x => optProfit P x γG) γP ∧
    DifferentiableAt ℝ (fun y => optProfit P γP y) γG ∧
    0 ≤ deriv (fun x => optProfit P x γG) γP ∧
    ((P.b0 - 2 * P.b1) * γP + P.b1 * γG < P.b0 * (cr P - dc P) →
        deriv (fun y => optProfit P γP y) γG < 0) ∧
    (P.b0 * (cr P - dc P) ≤ (P.b0 - 2 * P.b1) * γP + P.b1 * γG →
        0 ≤ deriv (fun y => optProfit P γP y) γG) ∧
    ((P.b0 - 2 * P.b1) * γP + P.b1 * γG < P.b0 * (cr P - dc P) ↔
        tauMStar P γP γG < P.b1 / P.b0) ∧
    (P.b0 * γG - P.b1 * γP ≤ P.b0 * (cr P - dc P) →
        deriv (fun y => optProfit P γP y) γG ≤ deriv (fun x => optProfit P x γG) γP) ∧
    (P.b0 * (cr P - dc P) < P.b0 * γG - P.b1 * γP →
        deriv (fun x => optProfit P x γG) γP < deriv (fun y => optProfit P γP y) γG) ∧
    (P.b0 * γG - P.b1 * γP ≤ P.b0 * (cr P - dc P) ↔
        tauMStar P γP γG ≤ (P.b0 + P.b1) / (2 * P.b0)) := by
  apply @PrideGuilt.theorem_2 <;> assumption

end PrideGuilt
