-- Prove2me | solution 1 for SepMeasures.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:29:50.997805+00:00
-- url     : https://prove2.me/submissions/c1178271-e576-4a66-9d20-aee34e94abef

import Mathlib
import Definitions.Def_SepMeasures_CutValue
import Definitions.Def_SepMeasures_Families

open MeasureTheory SepMeasures Filter Topology

namespace Aux31

noncomputable section

def e₀ : E 1 := EuclideanSpace.single 0 1

lemma e0_ne_zero : e₀ ≠ 0 := by
  intro h
  have : e₀ 0 = (0 : E 1) 0 := congrArg (fun v => v 0) h
  simp [e₀] at this

lemma norm_eq_abs_mul (N : Seminorm ℝ (E 1)) (z : E 1) :
    N z = |z 0| * N e₀ := by
  have hz : z = (z 0) • e₀ := by
    ext i; fin_cases i; simp [e₀]
  conv_lhs => rw [hz]
  rw [map_smul_eq_mul, Real.norm_eq_abs]

lemma N_e0_pos (N : Seminorm ℝ (E 1)) (hN : ∀ x, N x = 0 → x = 0) :
    0 < N e₀ := by
  refine lt_of_le_of_ne (apply_nonneg N _) (fun h => ?_)
  exact e0_ne_zero (hN _ h.symm)

lemma coe_nnnorm_eq_ofReal_abs (r : ℝ) : (‖r‖₊ : ENNReal) = ENNReal.ofReal |r| := by
  have h : |r| = (‖r‖₊ : ℝ) := by rw [coe_nnnorm, Real.norm_eq_abs]
  rw [h, ENNReal.ofReal_coe_nnreal]

lemma integrable_coord {μ : Measure (E 1)} [IsProbabilityMeasure μ]
    {N : Seminorm ℝ (E 1)} (hN : ∀ x, N x = 0 → x = 0) (hμ : FiniteFirstMoment N μ) :
    Integrable (fun x : E 1 => x 0) μ := by
  have hα : 0 < N e₀ := N_e0_pos N hN
  have hcont : Continuous (fun x : E 1 => x 0) := PiLp.continuous_apply 2 _ 0
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have hle : ∀ x : E 1, (‖x 0‖₊ : ENNReal) = ENNReal.ofReal ((N e₀)⁻¹) * ENNReal.ofReal (N x) := by
    intro x
    rw [coe_nnnorm_eq_ofReal_abs, norm_eq_abs_mul N x,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hα.le)]
    congr 1
    field_simp [hα.ne']
  have hmN : Measurable (fun x : E 1 => ENNReal.ofReal (N x)) := by
    have hN_eq : (fun x : E 1 => ENNReal.ofReal (N x)) =
        fun x => ENNReal.ofReal (|x 0| * N e₀) := funext fun x => by rw [norm_eq_abs_mul N x]
    rw [hN_eq]
    exact ENNReal.measurable_ofReal.comp ((continuous_abs.comp hcont).mul continuous_const).measurable
  calc ∫⁻ x, ‖x 0‖ₑ ∂μ
    _ ≤ ∫⁻ x, ENNReal.ofReal ((N e₀)⁻¹) * ENNReal.ofReal (N x) ∂μ :=
        lintegral_mono fun x => (hle x).le
    _ = ENNReal.ofReal ((N e₀)⁻¹) * ∫⁻ x, ENNReal.ofReal (N x) ∂μ :=
        lintegral_const_mul _ hmN
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ

def ltInd (t : ℝ) (z : ℝ) : ℝ := if z < t then 1 else 0

lemma measurable_ltInd (t : ℝ) : Measurable (ltInd t) :=
  Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const

lemma ltInd_bounds (t z : ℝ) : 0 ≤ ltInd t z ∧ |ltInd t z| ≤ 1 := by
  unfold ltInd
  split_ifs <;> norm_num

def rightCutInd (τ : ℝ) (a b : ℝ) : ℝ :=
  if (a < τ ∧ τ ≤ b) ∨ (b < τ ∧ τ ≤ a) then 1 else 0

lemma rightCut_decomp (τ a b : ℝ) :
    |a - b| * rightCutInd τ a b =
      max (τ - a) 0 + max (τ - b) 0 + (a - τ) * ltInd τ b + (b - τ) * ltInd τ a := by
  unfold rightCutInd ltInd
  by_cases ha : a < τ <;> by_cases hb : b < τ
  · have hna : ¬ τ ≤ a := not_le.mpr ha
    have hnb : ¬ τ ≤ b := not_le.mpr hb
    simp [ha, hb, hna, hnb, max_eq_left (sub_nonneg.mpr ha.le),
      max_eq_left (sub_nonneg.mpr hb.le)]
    ring
  · have hnb : τ ≤ b := not_lt.mp hb
    have hle : a ≤ b := ha.le.trans hnb
    simp [ha, hb, hnb, max_eq_left (sub_nonneg.mpr ha.le),
      abs_of_nonpos (sub_nonpos.mpr hle)]
  · have hna : τ ≤ a := not_lt.mp ha
    have hle : b ≤ a := hb.le.trans hna
    simp [ha, hb, hna, max_eq_left (sub_nonneg.mpr hb.le),
      abs_of_nonneg (sub_nonneg.mpr hle)]
  · have hna : τ ≤ a := not_lt.mp ha
    have hnb : τ ≤ b := not_lt.mp hb
    simp [ha, hb, max_eq_right (sub_nonpos.mpr hna), max_eq_right (sub_nonpos.mpr hnb)]

lemma phi_lower_bound {h u : ℝ} (hh : 0 ≤ h) :
    h - 2 * u ≤ max (-h - u) 0 + max (-u) 0 + max (h - u) 0 +
      2 * h * ltInd (-h) u + h * ltInd 0 u - |u| := by
  unfold ltInd
  by_cases h1 : u < -h
  · have h2 : u < 0 := by linarith
    simp [h1, h2, max_eq_left (by linarith : 0 ≤ -h - u),
      max_eq_left (by linarith : 0 ≤ -u), max_eq_left (by linarith : 0 ≤ h - u),
      abs_of_neg h2]
    linarith
  · by_cases h2 : u < 0
    · simp [h1, h2, max_eq_right (by linarith : -h - u ≤ 0),
        max_eq_left (by linarith : 0 ≤ -u), max_eq_left (by linarith : 0 ≤ h - u),
        abs_of_neg h2]
      linarith
    · by_cases h3 : u < h
      · simp [h1, h2, max_eq_right (by linarith : -h - u ≤ 0),
          max_eq_right (by linarith : -u ≤ 0), max_eq_left (by linarith : 0 ≤ h - u),
          abs_of_nonneg (not_lt.mp h2)]
        linarith
      · simp [h1, h2, max_eq_right (by linarith : -h - u ≤ 0),
          max_eq_right (by linarith : -u ≤ 0), max_eq_right (by linarith : h - u ≤ 0),
          abs_of_nonneg (not_lt.mp h2)]
        linarith

lemma psi_lower_bound {h v : ℝ} (hh : 0 ≤ h) :
    -2 * h - v ≤ max (-h - v) 0 + max (-v) 0 + max (h - v) 0 -
      h * ltInd 0 v - 2 * h * ltInd h v - |v| := by
  unfold ltInd
  by_cases h1 : v < -h
  · have h2 : v < 0 := by linarith
    have h3 : v < h := by linarith
    simp [h2, h3, max_eq_left (by linarith : 0 ≤ -h - v),
      max_eq_left (by linarith : 0 ≤ -v), max_eq_left (by linarith : 0 ≤ h - v),
      abs_of_neg h2]
    linarith
  · by_cases h2 : v < 0
    · have h3 : v < h := by linarith
      simp [h2, h3, max_eq_right (by linarith : -h - v ≤ 0),
        max_eq_left (by linarith : 0 ≤ -v), max_eq_left (by linarith : 0 ≤ h - v),
        abs_of_neg h2]
      linarith
    · by_cases h3 : v < h
      · simp [h2, h3, max_eq_right (by linarith : -h - v ≤ 0),
          max_eq_right (by linarith : -v ≤ 0), max_eq_left (by linarith : 0 ≤ h - v),
          abs_of_nonneg (not_lt.mp h2)]
        linarith
      · simp [h2, h3, max_eq_right (by linarith : -h - v ≤ 0),
          max_eq_right (by linarith : -v ≤ 0), max_eq_right (by linarith : h - v ≤ 0),
          abs_of_nonneg (not_lt.mp h2)]
        linarith

def Cprime (μ ν : Measure (E 1)) (τ : ℝ) : ℝ :=
  ∫ p, |p.1 0 - p.2 0| * rightCutInd τ (p.1 0) (p.2 0) ∂(μ.prod ν)

lemma Cprime_shifted_eq {μ ν : Measure (E 1)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : E 1 => x 0) μ) (hν : Integrable (fun y : E 1 => y 0) ν)
    (m₀ t : ℝ) :
    Cprime μ ν (m₀ + t) =
      (∫ x, (max (t - (x 0 - m₀)) 0 + ((∫ y, (y 0 - m₀) ∂ν) - t) * ltInd t (x 0 - m₀)) ∂μ) +
        ∫ y, (max (t - (y 0 - m₀)) 0 + ((∫ x, (x 0 - m₀) ∂μ) - t) * ltInd t (y 0 - m₀)) ∂ν := by
  unfold Cprime
  have hpt : ∀ p : E 1 × E 1,
      |p.1 0 - p.2 0| * rightCutInd (m₀ + t) (p.1 0) (p.2 0) =
        max (t - (p.1 0 - m₀)) 0 + max (t - (p.2 0 - m₀)) 0 +
          ((p.1 0 - m₀) - t) * ltInd t (p.2 0 - m₀) +
          ((p.2 0 - m₀) - t) * ltInd t (p.1 0 - m₀) := by
    intro ⟨x, y⟩
    have h1 := rightCut_decomp t (x 0 - m₀) (y 0 - m₀)
    have habs : |(x 0 - m₀) - (y 0 - m₀)| = |x 0 - y 0| := by congr 1; ring
    have hrc : rightCutInd t (x 0 - m₀) (y 0 - m₀) = rightCutInd (m₀ + t) (x 0) (y 0) := by
      unfold rightCutInd
      have e1 : (x 0 - m₀ < t ∧ t ≤ y 0 - m₀) ↔ (x 0 < m₀ + t ∧ m₀ + t ≤ y 0) := by
        constructor <;> rintro ⟨a, b⟩ <;> exact ⟨by linarith, by linarith⟩
      have e2 : (y 0 - m₀ < t ∧ t ≤ x 0 - m₀) ↔ (y 0 < m₀ + t ∧ m₀ + t ≤ x 0) := by
        constructor <;> rintro ⟨a, b⟩ <;> exact ⟨by linarith, by linarith⟩
      simp only [e1, e2]
    rw [habs, hrc] at h1
    exact h1
  simp_rw [hpt]
  have hu : Integrable (fun x : E 1 => x 0 - m₀) μ := hμ.sub (integrable_const m₀)
  have hv : Integrable (fun y : E 1 => y 0 - m₀) ν := hν.sub (integrable_const m₀)
  have i1x : Integrable (fun x : E 1 => max (t - (x 0 - m₀)) 0) μ :=
    ((integrable_const t).sub hu).sup (integrable_const 0)
  have i1y : Integrable (fun y : E 1 => max (t - (y 0 - m₀)) 0) ν :=
    ((integrable_const t).sub hv).sup (integrable_const 0)
  have iltx : Integrable (fun x : E 1 => ltInd t (x 0 - m₀)) μ := by
    refine Integrable.of_bound
      ((measurable_ltInd t).comp ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).sub
        continuous_const).measurable).aestronglyMeasurable
      1 (ae_of_all μ fun x => (ltInd_bounds t (x 0 - m₀)).2)
  have ilty : Integrable (fun y : E 1 => ltInd t (y 0 - m₀)) ν := by
    refine Integrable.of_bound
      ((measurable_ltInd t).comp ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).sub
        continuous_const).measurable).aestronglyMeasurable
      1 (ae_of_all ν fun y => (ltInd_bounds t (y 0 - m₀)).2)
  have p1 : Integrable (fun p : E 1 × E 1 => max (t - (p.1 0 - m₀)) 0 * (1 : ℝ)) (μ.prod ν) :=
    i1x.mul_prod (integrable_const 1)
  have p2 : Integrable (fun p : E 1 × E 1 => (1 : ℝ) * max (t - (p.2 0 - m₀)) 0) (μ.prod ν) :=
    (integrable_const 1).mul_prod i1y
  have q1 : Integrable (fun p : E 1 × E 1 => max (t - (p.1 0 - m₀)) 0) (μ.prod ν) := by
    simpa using p1
  have q2 : Integrable (fun p : E 1 × E 1 => max (t - (p.2 0 - m₀)) 0) (μ.prod ν) := by
    simpa using p2
  have q3 : Integrable (fun p : E 1 × E 1 => ((p.1 0 - m₀) - t) * ltInd t (p.2 0 - m₀)) (μ.prod ν) :=
    (hu.sub (integrable_const t)).mul_prod ilty
  have q4 : Integrable (fun p : E 1 × E 1 => ltInd t (p.1 0 - m₀) * ((p.2 0 - m₀) - t)) (μ.prod ν) :=
    iltx.mul_prod (hv.sub (integrable_const t))
  have q4' : Integrable (fun p : E 1 × E 1 => ((p.2 0 - m₀) - t) * ltInd t (p.1 0 - m₀)) (μ.prod ν) :=
    q4.congr (ae_of_all _ fun _ => mul_comm _ _)
  have q12 : Integrable (fun p : E 1 × E 1 =>
      max (t - (p.1 0 - m₀)) 0 + max (t - (p.2 0 - m₀)) 0) (μ.prod ν) := q1.add q2
  have q123 : Integrable (fun p : E 1 × E 1 =>
      max (t - (p.1 0 - m₀)) 0 + max (t - (p.2 0 - m₀)) 0 +
        ((p.1 0 - m₀) - t) * ltInd t (p.2 0 - m₀)) (μ.prod ν) := q12.add q3
  rw [integral_add q123 q4', integral_add q12 q3, integral_add q1 q2]
  have e_q1 : (∫ p : E 1 × E 1, max (t - (p.1 0 - m₀)) 0 ∂(μ.prod ν)) =
      ∫ x, max (t - (x 0 - m₀)) 0 ∂μ := by
    have := integral_prod_mul (μ := μ) (ν := ν) (fun x => max (t - (x 0 - m₀)) 0) (fun _ => (1 : ℝ))
    simpa [integral_const, probReal_univ] using this
  have e_q2 : (∫ p : E 1 × E 1, max (t - (p.2 0 - m₀)) 0 ∂(μ.prod ν)) =
      ∫ y, max (t - (y 0 - m₀)) 0 ∂ν := by
    have := integral_prod_mul (μ := μ) (ν := ν) (fun _ => (1 : ℝ)) (fun y => max (t - (y 0 - m₀)) 0)
    simpa [integral_const, probReal_univ] using this
  have e_q3 : (∫ p : E 1 × E 1, ((p.1 0 - m₀) - t) * ltInd t (p.2 0 - m₀) ∂(μ.prod ν)) =
      (∫ x, ((x 0 - m₀) - t) ∂μ) * ∫ y, ltInd t (y 0 - m₀) ∂ν :=
    integral_prod_mul (μ := μ) (ν := ν) (fun x => (x 0 - m₀) - t) (fun y => ltInd t (y 0 - m₀))
  have e_q4 : (∫ p : E 1 × E 1, ((p.2 0 - m₀) - t) * ltInd t (p.1 0 - m₀) ∂(μ.prod ν)) =
      (∫ y, ((y 0 - m₀) - t) ∂ν) * ∫ x, ltInd t (x 0 - m₀) ∂μ := by
    have hcomm : (∫ p : E 1 × E 1, ((p.2 0 - m₀) - t) * ltInd t (p.1 0 - m₀) ∂(μ.prod ν)) =
        ∫ p : E 1 × E 1, ltInd t (p.1 0 - m₀) * ((p.2 0 - m₀) - t) ∂(μ.prod ν) := by
      congr 1; ext p; ring
    rw [hcomm, integral_prod_mul (μ := μ) (ν := ν)
      (fun x => ltInd t (x 0 - m₀)) (fun y => (y 0 - m₀) - t), mul_comm]
  rw [e_q1, e_q2, e_q3, e_q4]
  have sub_u : (∫ x, ((x 0 - m₀) - t) ∂μ) = (∫ x, (x 0 - m₀) ∂μ) - t := by
    rw [integral_sub hu (integrable_const t), integral_const, probReal_univ, one_smul]
  have sub_v : (∫ y, ((y 0 - m₀) - t) ∂ν) = (∫ y, (y 0 - m₀) ∂ν) - t := by
    rw [integral_sub hv (integrable_const t), integral_const, probReal_univ, one_smul]
  rw [sub_u, sub_v, integral_add i1x (iltx.const_mul _), integral_add i1y (ilty.const_mul _),
    integral_const_mul, integral_const_mul]
  ring

lemma sum_three_Cprime_ge_ordered {μ ν : Measure (E 1)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : E 1 => x 0) μ) (hν : Integrable (fun y : E 1 => y 0) ν)
    (hord : (∫ x, x 0 ∂μ) ≤ ∫ y, y 0 ∂ν) :
    (∫ p, |p.1 0 - p.2 0| ∂(μ.prod ν)) ≤
      Cprime μ ν (∫ x, x 0 ∂μ) +
        Cprime μ ν (((∫ x, x 0 ∂μ) + ∫ y, y 0 ∂ν) / 2) +
        Cprime μ ν (∫ y, y 0 ∂ν) := by
  set mX := ∫ x, x 0 ∂μ
  set mY := ∫ y, y 0 ∂ν
  set m₀ := (mX + mY) / 2
  set h := (mY - mX) / 2
  have hh : 0 ≤ h := by dsimp [h]; linarith
  have hu : Integrable (fun x : E 1 => x 0 - m₀) μ := hμ.sub (integrable_const m₀)
  have hv : Integrable (fun y : E 1 => y 0 - m₀) ν := hν.sub (integrable_const m₀)
  have hm_u : ∫ x, (x 0 - m₀) ∂μ = -h := by
    rw [integral_sub hμ (integrable_const m₀), integral_const, probReal_univ, one_smul]
    dsimp [mX, m₀, h]; ring
  have hm_v : ∫ y, (y 0 - m₀) ∂ν = h := by
    rw [integral_sub hν (integrable_const m₀), integral_const, probReal_univ, one_smul]
    dsimp [mY, m₀, h]; ring
  have ht1 : Cprime μ ν mX = Cprime μ ν (m₀ + (-h)) := by congr 1; dsimp [m₀, h]; ring
  have ht2 : Cprime μ ν m₀ = Cprime μ ν (m₀ + 0) := by rw [add_zero]
  have ht3 : Cprime μ ν mY = Cprime μ ν (m₀ + h) := by congr 1; dsimp [m₀, h]; ring
  rw [ht1, ht2, ht3,
    Cprime_shifted_eq hμ hν m₀ (-h),
    Cprime_shifted_eq hμ hν m₀ 0,
    Cprime_shifted_eq hμ hν m₀ h,
    hm_u, hm_v]
  have ilt_x : ∀ t, Integrable (fun x : E 1 => ltInd t (x 0 - m₀)) μ := fun t =>
    Integrable.of_bound
      ((measurable_ltInd t).comp ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).sub
        continuous_const).measurable).aestronglyMeasurable
      1 (ae_of_all μ fun x => (ltInd_bounds t (x 0 - m₀)).2)
  have ilt_y : ∀ t, Integrable (fun y : E 1 => ltInd t (y 0 - m₀)) ν := fun t =>
    Integrable.of_bound
      ((measurable_ltInd t).comp ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).sub
        continuous_const).measurable).aestronglyMeasurable
      1 (ae_of_all ν fun y => (ltInd_bounds t (y 0 - m₀)).2)
  have imax_x : ∀ t, Integrable (fun x : E 1 => max (t - (x 0 - m₀)) 0) μ := fun t =>
    ((integrable_const t).sub hu).sup (integrable_const 0)
  have imax_y : ∀ t, Integrable (fun y : E 1 => max (t - (y 0 - m₀)) 0) ν := fun t =>
    ((integrable_const t).sub hv).sup (integrable_const 0)
  let termX (t : ℝ) (x : E 1) : ℝ := max (t - (x 0 - m₀)) 0 + (h - t) * ltInd t (x 0 - m₀)
  let termY (t : ℝ) (y : E 1) : ℝ := max (t - (y 0 - m₀)) 0 + (-h - t) * ltInd t (y 0 - m₀)
  have itX : ∀ t, Integrable (termX t) μ := fun t => (imax_x t).add ((ilt_x t).const_mul _)
  have itY : ∀ t, Integrable (termY t) ν := fun t => (imax_y t).add ((ilt_y t).const_mul _)
  have itX01 : Integrable (fun x => termX (-h) x + termX 0 x) μ := (itX (-h)).add (itX 0)
  have itY01 : Integrable (fun y => termY (-h) y + termY 0 y) ν := (itY (-h)).add (itY 0)
  have hsumX : (∫ x, termX (-h) x ∂μ) + (∫ x, termX 0 x ∂μ) + (∫ x, termX h x ∂μ) =
      ∫ x, (termX (-h) x + termX 0 x + termX h x) ∂μ := by
    rw [← integral_add (itX (-h)) (itX 0), ← integral_add itX01 (itX h)]
  have hsumY : (∫ y, termY (-h) y ∂ν) + (∫ y, termY 0 y ∂ν) + (∫ y, termY h y ∂ν) =
      ∫ y, (termY (-h) y + termY 0 y + termY h y) ∂ν := by
    rw [← integral_add (itY (-h)) (itY 0), ← integral_add itY01 (itY h)]
  have hphi_int : (∫ x, |x 0 - m₀| ∂μ) + 3 * h ≤
      ∫ x, (termX (-h) x + termX 0 x + termX h x) ∂μ := by
    have hpt : ∀ x : E 1, |x 0 - m₀| + (h - 2 * (x 0 - m₀)) ≤
        termX (-h) x + termX 0 x + termX h x := by
      intro x
      have hp := phi_lower_bound (u := x 0 - m₀) hh
      dsimp only [termX]
      have z1 : 0 - (x 0 - m₀) = -(x 0 - m₀) := zero_sub _
      have z2 : h - -h = 2 * h := by ring
      have z3 : h - 0 = h := sub_zero h
      have z4 : (h - h) * ltInd h (x 0 - m₀) = 0 := by simp
      rw [z1, z2, z3, z4]
      linarith
    have i2u : Integrable (fun x : E 1 => 2 * (x 0 - m₀)) μ := hu.const_mul 2
    have ih2u : Integrable (fun x : E 1 => h - 2 * (x 0 - m₀)) μ := (integrable_const h).sub i2u
    have ilhs : Integrable (fun x : E 1 => |x 0 - m₀| + (h - 2 * (x 0 - m₀))) μ :=
      hu.abs.add ih2u
    have irhs : Integrable (fun x : E 1 => termX (-h) x + termX 0 x + termX h x) μ :=
      itX01.add (itX h)
    have hmono := integral_mono ilhs irhs hpt
    rw [integral_add hu.abs ih2u, integral_sub (integrable_const h) i2u,
      integral_const, probReal_univ, one_smul, integral_const_mul, hm_u] at hmono
    linarith
  have hpsi_int : (∫ y, |y 0 - m₀| ∂ν) - 3 * h ≤
      ∫ y, (termY (-h) y + termY 0 y + termY h y) ∂ν := by
    have hpt : ∀ y : E 1, |y 0 - m₀| + (-2 * h - (y 0 - m₀)) ≤
        termY (-h) y + termY 0 y + termY h y := by
      intro y
      have hp := psi_lower_bound (v := y 0 - m₀) hh
      dsimp only [termY]
      have z1 : 0 - (y 0 - m₀) = -(y 0 - m₀) := zero_sub _
      have z2 : (-h - -h) * ltInd (-h) (y 0 - m₀) = 0 := by simp
      have z3 : -h - 0 = -h := sub_zero _
      have z4 : -h - h = -(2 * h) := by ring
      rw [z1, z2, z3, z4]
      linarith
    have ihv : Integrable (fun y : E 1 => -2 * h - (y 0 - m₀)) ν := (integrable_const (-2 * h)).sub hv
    have ilhs : Integrable (fun y : E 1 => |y 0 - m₀| + (-2 * h - (y 0 - m₀))) ν :=
      hv.abs.add ihv
    have irhs : Integrable (fun y : E 1 => termY (-h) y + termY 0 y + termY h y) ν :=
      itY01.add (itY h)
    have hmono := integral_mono ilhs irhs hpt
    rw [integral_add hv.abs ihv, integral_sub (integrable_const (-2 * h)) hv,
      integral_const, probReal_univ, one_smul, hm_v] at hmono
    linarith
  have htri : (∫ p, |p.1 0 - p.2 0| ∂(μ.prod ν)) ≤
      (∫ x, |x 0 - m₀| ∂μ) + ∫ y, |y 0 - m₀| ∂ν := by
    have ip1 : Integrable (fun p : E 1 × E 1 => |p.1 0 - m₀| * (1 : ℝ)) (μ.prod ν) :=
      hu.abs.mul_prod (integrable_const 1)
    have ip2 : Integrable (fun p : E 1 × E 1 => (1 : ℝ) * |p.2 0 - m₀|) (μ.prod ν) :=
      (integrable_const 1).mul_prod hv.abs
    have iq1 : Integrable (fun p : E 1 × E 1 => |p.1 0 - m₀|) (μ.prod ν) := by simpa using ip1
    have iq2 : Integrable (fun p : E 1 × E 1 => |p.2 0 - m₀|) (μ.prod ν) := by simpa using ip2
    have idiff : Integrable (fun p : E 1 × E 1 => |p.1 0 - p.2 0|) (μ.prod ν) := by
      have ipx : Integrable (fun p : E 1 × E 1 => p.1 0 * (1 : ℝ)) (μ.prod ν) :=
        hμ.mul_prod (integrable_const 1)
      have ipy : Integrable (fun p : E 1 × E 1 => (1 : ℝ) * p.2 0) (μ.prod ν) :=
        (integrable_const 1).mul_prod hν
      have iqx : Integrable (fun p : E 1 × E 1 => p.1 0) (μ.prod ν) := by simpa using ipx
      have iqy : Integrable (fun p : E 1 × E 1 => p.2 0) (μ.prod ν) := by simpa using ipy
      exact (iqx.sub iqy).abs
    have hmono : (∫ p, |p.1 0 - p.2 0| ∂(μ.prod ν)) ≤
        ∫ p, (|p.1 0 - m₀| + |p.2 0 - m₀|) ∂(μ.prod ν) := by
      refine integral_mono idiff (iq1.add iq2) fun ⟨x, y⟩ => ?_
      have : x 0 - y 0 = (x 0 - m₀) - (y 0 - m₀) := by ring
      rw [this]
      exact abs_sub _ _
    rw [integral_add iq1 iq2] at hmono
    have eq1 : (∫ p : E 1 × E 1, |p.1 0 - m₀| ∂(μ.prod ν)) = ∫ x, |x 0 - m₀| ∂μ := by
      have := integral_prod_mul (μ := μ) (ν := ν) (fun x => |x 0 - m₀|) (fun _ => (1 : ℝ))
      simpa [integral_const, probReal_univ] using this
    have eq2 : (∫ p : E 1 × E 1, |p.2 0 - m₀| ∂(μ.prod ν)) = ∫ y, |y 0 - m₀| ∂ν := by
      have := integral_prod_mul (μ := μ) (ν := ν) (fun _ => (1 : ℝ)) (fun y => |y 0 - m₀|)
      simpa [integral_const, probReal_univ] using this
    linarith
  change (∫ p, |p.1 0 - p.2 0| ∂(μ.prod ν)) ≤
    ((∫ x, termX (-h) x ∂μ) + ∫ y, termY (-h) y ∂ν) +
      ((∫ x, termX 0 x ∂μ) + ∫ y, termY 0 y ∂ν) +
      ((∫ x, termX h x ∂μ) + ∫ y, termY h y ∂ν)
  linarith [hsumX, hsumY, hphi_int, hpsi_int, htri]

lemma Cprime_comm (μ ν : Measure (E 1)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (τ : ℝ) :
    Cprime μ ν τ = Cprime ν μ τ := by
  unfold Cprime
  rw [← Measure.prod_swap (μ := ν) (ν := μ)]
  have cx : Measurable (fun p : E 1 × E 1 => p.1 0) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp continuous_fst).measurable
  have cy : Measurable (fun p : E 1 × E 1 => p.2 0) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp continuous_snd).measurable
  have ms : MeasurableSet {p : E 1 × E 1 | (p.1 0 < τ ∧ τ ≤ p.2 0) ∨ (p.2 0 < τ ∧ τ ≤ p.1 0)} :=
    ((measurableSet_lt cx measurable_const).inter (measurableSet_le measurable_const cy)).union
      ((measurableSet_lt cy measurable_const).inter (measurableSet_le measurable_const cx))
  have hmeas : Measurable (fun p : E 1 × E 1 => |p.1 0 - p.2 0| * rightCutInd τ (p.1 0) (p.2 0)) :=
    (continuous_abs.measurable.comp (cx.sub cy)).mul (Measurable.ite ms measurable_const measurable_const)
  rw [integral_map measurable_swap.aemeasurable hmeas.aestronglyMeasurable]
  congr 1
  ext ⟨y, x⟩
  simp only [Prod.swap, abs_sub_comm, rightCutInd]
  by_cases h1 : x 0 < τ ∧ τ ≤ y 0 <;> by_cases h2 : y 0 < τ ∧ τ ≤ x 0 <;> simp [h1, h2]

lemma totalDist_abs_comm (μ ν : Measure (E 1)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (∫ p, |p.1 0 - p.2 0| ∂(μ.prod ν)) = ∫ p, |p.1 0 - p.2 0| ∂(ν.prod μ) := by
  rw [← Measure.prod_swap (μ := ν) (ν := μ)]
  have hcont : Continuous (fun p : E 1 × E 1 => |p.1 0 - p.2 0|) :=
    continuous_abs.comp (((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp continuous_fst).sub
      ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp continuous_snd))
  rw [integral_map measurable_swap.aemeasurable hcont.aestronglyMeasurable]
  congr 1
  ext ⟨y, x⟩
  simp [Prod.swap, abs_sub_comm]

lemma tendsto_cutVal_left {μ ν : Measure (E 1)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {N : Seminorm ℝ (E 1)} (_hN : ∀ x, N x = 0 → x = 0)
    (hμ : Integrable (fun x : E 1 => x 0) μ) (hν : Integrable (fun y : E 1 => y 0) ν) (τ : ℝ) :
    Tendsto (fun k : ℕ => cutVal N μ ν ⟨e₀, τ - 1 / ((k : ℝ) + 1), e0_ne_zero⟩)
      atTop (𝓝 (N e₀ * Cprime μ ν τ)) := by
  have hrewrite : ∀ s : ℝ, cutVal N μ ν ⟨e₀, s, e0_ne_zero⟩ =
      N e₀ * ∫ p, |p.1 0 - p.2 0| *
        (SepMeasures.Sep (⟨e₀, s, e0_ne_zero⟩ : Hyp 1)).indicator (1 : E 1 × E 1 → ℝ) p ∂(μ.prod ν) := by
    intro s
    unfold cutVal
    have hms : MeasurableSet (SepMeasures.Sep (⟨e₀, s, e0_ne_zero⟩ : Hyp 1)) := by
      refine ((isOpen_lt continuous_const (continuous_const.inner continuous_id)).measurableSet.prod
        (isOpen_lt (continuous_const.inner continuous_id) continuous_const).measurableSet).union
        ((isOpen_lt (continuous_const.inner continuous_id) continuous_const).measurableSet.prod
        (isOpen_lt continuous_const (continuous_const.inner continuous_id)).measurableSet)
    rw [← integral_indicator hms]
    have hfn : (fun p : E 1 × E 1 => (SepMeasures.Sep (⟨e₀, s, e0_ne_zero⟩ : Hyp 1)).indicator
        (fun q => N (q.1 - q.2)) p) =
        fun p => N e₀ * (|p.1 0 - p.2 0| *
          (SepMeasures.Sep (⟨e₀, s, e0_ne_zero⟩ : Hyp 1)).indicator (1 : E 1 × E 1 → ℝ) p) := by
      ext p
      by_cases hp : p ∈ SepMeasures.Sep (⟨e₀, s, e0_ne_zero⟩ : Hyp 1)
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Pi.one_apply,
          norm_eq_abs_mul N (p.1 - p.2), PiLp.sub_apply]
        ring
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, mul_zero, mul_zero]
    rw [hfn, integral_const_mul]
  simp_rw [hrewrite]
  refine Filter.Tendsto.const_mul (N e₀) ?_
  unfold Cprime
  have idiff : Integrable (fun p : E 1 × E 1 => |p.1 0 - p.2 0|) (μ.prod ν) := by
    have ipx : Integrable (fun p : E 1 × E 1 => p.1 0 * (1 : ℝ)) (μ.prod ν) :=
      hμ.mul_prod (integrable_const 1)
    have ipy : Integrable (fun p : E 1 × E 1 => (1 : ℝ) * p.2 0) (μ.prod ν) :=
      (integrable_const 1).mul_prod hν
    have iqx : Integrable (fun p : E 1 × E 1 => p.1 0) (μ.prod ν) := by simpa using ipx
    have iqy : Integrable (fun p : E 1 × E 1 => p.2 0) (μ.prod ν) := by simpa using ipy
    exact (iqx.sub iqy).abs
  refine tendsto_integral_of_dominated_convergence (fun p => |p.1 0 - p.2 0|) ?_ idiff ?_ ?_
  · intro k
    have hms : MeasurableSet (SepMeasures.Sep (⟨e₀, τ - 1 / ((k : ℝ) + 1), e0_ne_zero⟩ : Hyp 1)) := by
      refine ((isOpen_lt continuous_const (continuous_const.inner continuous_id)).measurableSet.prod
        (isOpen_lt (continuous_const.inner continuous_id) continuous_const).measurableSet).union
        ((isOpen_lt (continuous_const.inner continuous_id) continuous_const).measurableSet.prod
        (isOpen_lt continuous_const (continuous_const.inner continuous_id)).measurableSet)
    have hcont : Continuous (fun p : E 1 × E 1 => |p.1 0 - p.2 0|) :=
      continuous_abs.comp (((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp continuous_fst).sub
        ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp continuous_snd))
    exact (hcont.measurable.mul (measurable_const.indicator hms)).aestronglyMeasurable
  · intro k
    refine ae_of_all _ fun p => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_abs]
    by_cases hp : p ∈ SepMeasures.Sep (⟨e₀, τ - 1 / ((k : ℝ) + 1), e0_ne_zero⟩ : Hyp 1)
    · rw [Set.indicator_of_mem hp, Pi.one_apply, abs_one, mul_one]
    · rw [Set.indicator_of_notMem hp, abs_zero, mul_zero]; exact abs_nonneg _
  · refine ae_of_all _ fun ⟨x, y⟩ => ?_
    refine tendsto_const_nhds.congr' ?_
    have hinner : ∀ z : E 1, inner ℝ e₀ z = z 0 := by
      intro z
      simp [e₀, EuclideanSpace.inner_eq_star_dotProduct]
    have hsep_iff : ∀ s : ℝ, (x, y) ∈ SepMeasures.Sep (⟨e₀, s, e0_ne_zero⟩ : Hyp 1) ↔
        (s < x 0 ∧ y 0 < s) ∨ (x 0 < s ∧ s < y 0) := by
      intro s
      simp [SepMeasures.Sep, Hyp.pos, Hyp.neg, hinner]
    by_cases hx : x 0 < τ <;> by_cases hy : y 0 < τ
    · obtain ⟨K, hK⟩ := exists_nat_gt (1 / (τ - max (x 0) (y 0)))
      refine eventually_atTop.mpr ⟨K, fun k hk => ?_⟩
      have hpos : 0 < τ - max (x 0) (y 0) := sub_pos.mpr (max_lt hx hy)
      have hk_gt : 1 / (τ - max (x 0) (y 0)) < (k : ℝ) + 1 :=
        hK.trans_le (by exact_mod_cast Nat.le_succ_of_le hk)
      have hinv : 1 / ((k : ℝ) + 1) < τ - max (x 0) (y 0) :=
        (div_lt_iff₀ (by positivity)).mpr ((div_lt_iff₀ hpos).mp hk_gt |>.trans_eq (mul_comm _ _))
      have hsx : x 0 < τ - 1 / ((k : ℝ) + 1) := by linarith [le_max_left (x 0) (y 0)]
      have hsy : y 0 < τ - 1 / ((k : ℝ) + 1) := by linarith [le_max_right (x 0) (y 0)]
      have hnot : (x, y) ∉ SepMeasures.Sep (⟨e₀, τ - 1 / ((k : ℝ) + 1), e0_ne_zero⟩ : Hyp 1) := by
        rw [hsep_iff]
        push Not
        exact ⟨fun h => by linarith, fun _ => by linarith⟩
      have hrc : rightCutInd τ (x 0) (y 0) = 0 := by
        unfold rightCutInd
        simp [hx, hy, not_le.mpr hx, not_le.mpr hy]
      dsimp only
      rw [Set.indicator_of_notMem hnot, hrc]
    · obtain ⟨K, hK⟩ := exists_nat_gt (1 / (τ - x 0))
      refine eventually_atTop.mpr ⟨K, fun k hk => ?_⟩
      have hpos : 0 < τ - x 0 := sub_pos.mpr hx
      have hk_gt : 1 / (τ - x 0) < (k : ℝ) + 1 :=
        hK.trans_le (by exact_mod_cast Nat.le_succ_of_le hk)
      have hinv : 1 / ((k : ℝ) + 1) < τ - x 0 :=
        (div_lt_iff₀ (by positivity)).mpr ((div_lt_iff₀ hpos).mp hk_gt |>.trans_eq (mul_comm _ _))
      have hsx : x 0 < τ - 1 / ((k : ℝ) + 1) := by linarith
      have hsy : τ - 1 / ((k : ℝ) + 1) < y 0 := by
        have hpos_k : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith [not_lt.mp hy]
      have hmem : (x, y) ∈ SepMeasures.Sep (⟨e₀, τ - 1 / ((k : ℝ) + 1), e0_ne_zero⟩ : Hyp 1) := by
        rw [hsep_iff]; exact Or.inr ⟨hsx, hsy⟩
      have hrc : rightCutInd τ (x 0) (y 0) = 1 := by
        unfold rightCutInd; simp [hx, not_lt.mp hy]
      dsimp only
      rw [Set.indicator_of_mem hmem, Pi.one_apply, hrc]
    · obtain ⟨K, hK⟩ := exists_nat_gt (1 / (τ - y 0))
      refine eventually_atTop.mpr ⟨K, fun k hk => ?_⟩
      have hpos : 0 < τ - y 0 := sub_pos.mpr hy
      have hk_gt : 1 / (τ - y 0) < (k : ℝ) + 1 :=
        hK.trans_le (by exact_mod_cast Nat.le_succ_of_le hk)
      have hinv : 1 / ((k : ℝ) + 1) < τ - y 0 :=
        (div_lt_iff₀ (by positivity)).mpr ((div_lt_iff₀ hpos).mp hk_gt |>.trans_eq (mul_comm _ _))
      have hsy : y 0 < τ - 1 / ((k : ℝ) + 1) := by linarith
      have hsx : τ - 1 / ((k : ℝ) + 1) < x 0 := by
        have hpos_k : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith [not_lt.mp hx]
      have hmem : (x, y) ∈ SepMeasures.Sep (⟨e₀, τ - 1 / ((k : ℝ) + 1), e0_ne_zero⟩ : Hyp 1) := by
        rw [hsep_iff]; exact Or.inl ⟨hsx, hsy⟩
      have hrc : rightCutInd τ (x 0) (y 0) = 1 := by
        unfold rightCutInd; simp [hy, not_lt.mp hx]
      dsimp only
      rw [Set.indicator_of_mem hmem, Pi.one_apply, hrc]
    · refine eventually_atTop.mpr ⟨0, fun k _ => ?_⟩
      have hpos_k : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hsx : τ - 1 / ((k : ℝ) + 1) < x 0 := by linarith [not_lt.mp hx]
      have hsy : τ - 1 / ((k : ℝ) + 1) < y 0 := by linarith [not_lt.mp hy]
      have hnot : (x, y) ∉ SepMeasures.Sep (⟨e₀, τ - 1 / ((k : ℝ) + 1), e0_ne_zero⟩ : Hyp 1) := by
        rw [hsep_iff]
        push Not
        exact ⟨fun _ => by linarith, fun h => by linarith⟩
      have hrc : rightCutInd τ (x 0) (y 0) = 0 := by
        unfold rightCutInd; simp [hx, hy]
      dsimp only
      rw [Set.indicator_of_notMem hnot, hrc]

end

end Aux31

theorem solution (N : Seminorm ℝ (E 1)) (hN : ∀ x, N x = 0 → x = 0) :
    (1 / 3 : ℝ) ≤ cutRatio N (Pf 1 N) := by
  unfold cutRatio
  have hne : Nonempty {p : Measure (E 1) × Measure (E 1) //
      p ∈ Pf 1 N ∧ 0 < totalDist N p.1 p.2} := by
    refine ⟨⟨(Measure.dirac 0, Measure.dirac Aux31.e₀), ?_, ?_⟩⟩
    · refine ⟨inferInstance, inferInstance, ?_, ?_⟩ <;>
        simp [FiniteFirstMoment, lintegral_dirac]
    · simp only [totalDist]
      rw [Measure.dirac_prod_dirac, integral_dirac, Aux31.norm_eq_abs_mul N]
      have hα := Aux31.N_e0_pos N hN
      have habs : |((0 : E 1) - Aux31.e₀) 0| = 1 := by simp [Aux31.e₀]
      rw [habs, one_mul]
      exact hα
  refine le_ciInf fun ⟨⟨μ, ν⟩, ⟨hprobμ, hprobν, hffmμ, hffmν⟩, hL⟩ => ?_
  have : IsProbabilityMeasure μ := hprobμ
  have : IsProbabilityMeasure ν := hprobν
  have hμ := Aux31.integrable_coord hN hffmμ
  have hν := Aux31.integrable_coord hN hffmν
  have idist : Integrable (fun p : E 1 × E 1 => N (p.1 - p.2)) (μ.prod ν) := by
    have ipx : Integrable (fun p : E 1 × E 1 => p.1 0 * (1 : ℝ)) (μ.prod ν) :=
      hμ.mul_prod (integrable_const 1)
    have ipy : Integrable (fun p : E 1 × E 1 => (1 : ℝ) * p.2 0) (μ.prod ν) :=
      (integrable_const 1).mul_prod hν
    have iqx : Integrable (fun p : E 1 × E 1 => p.1 0) (μ.prod ν) := by simpa using ipx
    have iqy : Integrable (fun p : E 1 × E 1 => p.2 0) (μ.prod ν) := by simpa using ipy
    have iabs := ((iqx.sub iqy).abs).mul_const (N Aux31.e₀)
    refine iabs.congr (ae_of_all _ fun p => ?_)
    simp [Aux31.norm_eq_abs_mul N (p.1 - p.2), PiLp.sub_apply]
  have hbdd : BddAbove (Set.range fun H : Hyp 1 => cutVal N μ ν H / totalDist N μ ν) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨H, rfl⟩
    have hle : cutVal N μ ν H ≤ totalDist N μ ν :=
      setIntegral_le_integral idist (ae_of_all _ fun _ => apply_nonneg N _)
    exact (div_le_one hL).mpr hle
  have htotal_eq : totalDist N μ ν = N Aux31.e₀ * ∫ p, |p.1 0 - p.2 0| ∂(μ.prod ν) := by
    unfold totalDist
    have hfn : (fun p : E 1 × E 1 => N (p.1 - p.2)) =
        fun p => N Aux31.e₀ * |p.1 0 - p.2 0| := by
      ext p
      rw [Aux31.norm_eq_abs_mul N (p.1 - p.2), PiLp.sub_apply, mul_comm]
    rw [hfn, integral_const_mul]
  have hsum : (∫ p, |p.1 0 - p.2 0| ∂(μ.prod ν)) ≤
      Aux31.Cprime μ ν (∫ x, x 0 ∂μ) +
        Aux31.Cprime μ ν (((∫ x, x 0 ∂μ) + ∫ y, y 0 ∂ν) / 2) +
        Aux31.Cprime μ ν (∫ y, y 0 ∂ν) := by
    rcases le_total (∫ x, x 0 ∂μ) (∫ y, y 0 ∂ν) with hle | hge
    · exact Aux31.sum_three_Cprime_ge_ordered hμ hν hle
    · have hswap := Aux31.sum_three_Cprime_ge_ordered hν hμ hge
      rw [← Aux31.totalDist_abs_comm μ ν,
        ← Aux31.Cprime_comm μ ν,
        ← Aux31.Cprime_comm μ ν (((∫ y, y 0 ∂ν) + ∫ x, x 0 ∂μ) / 2),
        ← Aux31.Cprime_comm μ ν (∫ x, x 0 ∂μ)] at hswap
      have hmid : ((∫ y, y 0 ∂ν) + ∫ x, x 0 ∂μ) / 2 =
          ((∫ x, x 0 ∂μ) + ∫ y, y 0 ∂ν) / 2 := by ring
      rw [hmid] at hswap
      linarith
  have hC_le_sup : ∀ τ : ℝ, N Aux31.e₀ * Aux31.Cprime μ ν τ / totalDist N μ ν ≤
      ⨆ H : Hyp 1, cutVal N μ ν H / totalDist N μ ν := by
    intro τ
    have htend := (Aux31.tendsto_cutVal_left hN hμ hν τ).div_const (totalDist N μ ν)
    refine le_of_tendsto htend (Eventually.of_forall fun k => ?_)
    exact le_ciSup hbdd ⟨Aux31.e₀, τ - 1 / ((k : ℝ) + 1), Aux31.e0_ne_zero⟩
  have h1 := hC_le_sup (∫ x, x 0 ∂μ)
  have h2 := hC_le_sup (((∫ x, x 0 ∂μ) + ∫ y, y 0 ∂ν) / 2)
  have h3 := hC_le_sup (∫ y, y 0 ∂ν)
  have hα := Aux31.N_e0_pos N hN
  have hsum_scaled : totalDist N μ ν ≤
      N Aux31.e₀ * Aux31.Cprime μ ν (∫ x, x 0 ∂μ) +
        N Aux31.e₀ * Aux31.Cprime μ ν (((∫ x, x 0 ∂μ) + ∫ y, y 0 ∂ν) / 2) +
        N Aux31.e₀ * Aux31.Cprime μ ν (∫ y, y 0 ∂ν) := by
    rw [htotal_eq]
    have := mul_le_mul_of_nonneg_left hsum hα.le
    linarith
  have hdiv_sum : 1 ≤
      N Aux31.e₀ * Aux31.Cprime μ ν (∫ x, x 0 ∂μ) / totalDist N μ ν +
        N Aux31.e₀ * Aux31.Cprime μ ν (((∫ x, x 0 ∂μ) + ∫ y, y 0 ∂ν) / 2) / totalDist N μ ν +
        N Aux31.e₀ * Aux31.Cprime μ ν (∫ y, y 0 ∂ν) / totalDist N μ ν := by
    rw [← add_div, ← add_div, one_le_div hL]
    exact hsum_scaled
  linarith
