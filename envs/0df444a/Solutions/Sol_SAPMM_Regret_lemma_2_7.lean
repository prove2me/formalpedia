-- Prove2me | solution 1 for SAPMM.Regret.lemma_2_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:25:47.943555+00:00
-- url     : https://prove2.me/submissions/829d4e4d-33ad-4b8f-a032-49611f8f4ef2

import Mathlib
import Definitions.Def_SAPMM_Regret_Model

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret.AuxE

lemma exp_le_quad {y : ℝ} (hy : |y| ≤ 1) : Real.exp y ≤ 1 + y + y ^ 2 := by
  have := Real.abs_exp_sub_one_sub_id_le hy
  have := le_abs_self (Real.exp y - 1 - y)
  linarith

lemma exp_ge_tangent (a b : ℝ) : Real.exp a * (1 + (b - a)) ≤ Real.exp b := by
  have h := Real.add_one_le_exp (b - a)
  have := mul_le_mul_of_nonneg_left h (Real.exp_pos a).le
  rw [← Real.exp_add, show a + (b - a) = b by ring] at this
  linarith

end SAPMM.Regret.AuxE

open SAPMM.Regret.AuxE

theorem solution {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (hℱ0 : ℱ 0 = ⊥) (Z : ℕ → Ω → ℝ) (hZ : Adapted ℱ Z)
    (hZ0 : ∀ ω, Z 0 ω = 0) (t0 : ℕ) (ht0 : 1 ≤ t0) (θ δmax ζ : ℝ) (hθ : 0 < θ)
    (hδ : 0 < δmax) (hζ : 0 < ζ) (hζδ : ζ ≤ δmax)
    (hinc : ∀ t ω, |Z (t + 1) ω - Z t ω| ≤ δmax)
    (hdrift : ∀ t, 1 ≤ t → ∀ᵐ ω ∂μ,
      μ[fun ω => Z (t + t0) ω - Z t ω | ℱ t] ω ≤
        if Z t ω < θ then (t0 : ℝ) * δmax else -((t0 : ℝ) * ζ)) :
    ∀ t, 1 ≤ t → ∫ ω, Z t ω ∂μ ≤
      θ + t0 * δmax + t0 * (4 * δmax ^ 2 / ζ) * Real.log (8 * δmax ^ 2 / ζ ^ 2) := by
  have ht0' : (1 : ℝ) ≤ t0 := by exact_mod_cast ht0
  have hZm : ∀ t, Measurable (Z t) := fun t => (hZ t).mono (ℱ.le t) le_rfl
  -- increments over k steps
  have hincK : ∀ s k ω, |Z (s + k) ω - Z s ω| ≤ k * δmax := by
    intro s k ω
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 := hinc (s + k) ω
      rw [← add_assoc]
      calc |Z (s + k + 1) ω - Z s ω| = |(Z (s + k + 1) ω - Z (s + k) ω) + (Z (s + k) ω - Z s ω)| := by
            ring_nf
        _ ≤ |Z (s + k + 1) ω - Z (s + k) ω| + |Z (s + k) ω - Z s ω| := abs_add_le _ _
        _ ≤ δmax + k * δmax := add_le_add h1 ih
        _ = ((k + 1 : ℕ) : ℝ) * δmax := by push_cast; ring
  have hZb : ∀ t ω, |Z t ω| ≤ t * δmax := by
    intro t ω
    have := hincK 0 t ω
    rw [zero_add, hZ0, sub_zero] at this
    exact this
  -- the exponent
  set r := ζ / (4 * t0 * δmax ^ 2) with hr_def
  have hr : 0 < r := by positivity
  have hrt0 : r * t0 * δmax = ζ / (4 * δmax) := by
    rw [hr_def]; field_simp
  have hrt0le : r * t0 * δmax ≤ 1 := by
    rw [hrt0, div_le_one (by positivity)]; linarith
  set E := Real.exp (r * (θ + t0 * δmax)) with hE
  set ρ := 1 - ζ ^ 2 / (8 * δmax ^ 2) with hρ
  have hρ0 : 0 ≤ ρ := by
    rw [hρ, sub_nonneg, div_le_one (by positivity)]
    nlinarith
  have hρ1 : 1 - ρ = ζ ^ 2 / (8 * δmax ^ 2) := by rw [hρ]; ring
  have hρpos : 0 < 1 - ρ := by rw [hρ1]; positivity
  set B := E / (1 - ρ) with hB
  have hEB : E ≤ B := by
    rw [hB, le_div_iff₀ hρpos]
    have : 0 < E := Real.exp_pos _
    nlinarith
  have hexpint : ∀ s, Integrable (fun ω => Real.exp (r * Z s ω)) μ := by
    intro s
    refine Integrable.of_bound ((hZm s).const_mul r).exp.aestronglyMeasurable
      (Real.exp (r * (s * δmax))) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    have := (abs_le.1 (hZb s ω)).2
    exact mul_le_mul_of_nonneg_left this hr.le
  -- one block of t0 steps
  have hstep : ∀ s, 1 ≤ s →
      ∫ ω, Real.exp (r * Z (s + t0) ω) ∂μ ≤ ρ * ∫ ω, Real.exp (r * Z s ω) ∂μ + E := by
    intro s hs
    set A : Set Ω := {ω | θ ≤ Z s ω} with hA
    have hAm : MeasurableSet[ℱ s] A := measurableSet_le measurable_const (hZ s)
    set g : Ω → ℝ := A.indicator (fun ω => Real.exp (r * Z s ω)) with hg
    have hg_sm : StronglyMeasurable[ℱ s] g :=
      ((((hZ s).const_mul r).exp).indicator hAm).stronglyMeasurable
    have hg_m : Measurable g := (hg_sm.mono (ℱ.le s)).measurable
    have hg0 : ∀ ω, 0 ≤ g ω := fun ω => Set.indicator_nonneg (fun ω _ => (Real.exp_pos _).le) ω
    have hgle : ∀ ω, g ω ≤ Real.exp (r * Z s ω) := fun ω =>
      Set.indicator_le_self' (fun ω _ => (Real.exp_pos _).le) ω
    have hgb : ∀ ω, ‖g ω‖ ≤ Real.exp (r * (s * δmax)) := by
      intro ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 ω)]
      refine le_trans (hgle ω) ?_
      rw [Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left (abs_le.1 (hZb s ω)).2 hr.le
    have hgint : Integrable g μ :=
      Integrable.of_bound hg_m.aestronglyMeasurable _ (Filter.Eventually.of_forall hgb)
    set Δ : Ω → ℝ := fun ω => Z (s + t0) ω - Z s ω with hΔ
    have hΔm : Measurable Δ := (hZm (s + t0)).sub (hZm s)
    have hΔb : ∀ ω, |Δ ω| ≤ t0 * δmax := fun ω => hincK s t0 ω
    have hΔint : Integrable Δ μ :=
      Integrable.of_bound hΔm.aestronglyMeasurable _ (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact hΔb ω)
    have hgΔint : Integrable (g * Δ) μ := by
      have := hΔint.bdd_mul hg_m.aestronglyMeasurable (Filter.Eventually.of_forall hgb)
      exact this
    -- tower: ∫ gΔ = ∫ g E[Δ|ℱ s]
    have hkey1 : ∫ ω, (g * Δ) ω ∂μ = ∫ ω, (g * μ[Δ | ℱ s]) ω ∂μ := by
      rw [← integral_condExp (ℱ.le s)]
      exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hg_sm hgΔint hΔint)
    have hcint : Integrable (fun ω => g ω * μ[Δ | ℱ s] ω) μ :=
      integrable_condExp.bdd_mul hg_m.aestronglyMeasurable (Filter.Eventually.of_forall hgb)
    have hkey2 : ∫ ω, (g * μ[Δ | ℱ s]) ω ∂μ ≤ ∫ ω, -((t0 : ℝ) * ζ) * g ω ∂μ := by
      apply integral_mono_ae hcint (hgint.const_mul _)
      filter_upwards [hdrift s hs] with ω hω
      by_cases hωA : ω ∈ A
      · have hZs : ¬ Z s ω < θ := not_lt.2 hωA
        rw [if_neg hZs] at hω
        have := mul_le_mul_of_nonneg_left hω (hg0 ω)
        linarith
      · have : g ω = 0 := Set.indicator_of_notMem hωA _
        rw [this]; simp
    -- pointwise bound
    set c' := 1 + r ^ 2 * ((t0 : ℝ) * δmax) ^ 2 with hc'
    have hpt : ∀ ω, Real.exp (r * Z (s + t0) ω) ≤ E + c' * g ω + r * (g * Δ) ω := by
      intro ω
      simp only [Pi.mul_apply]
      by_cases hωA : ω ∈ A
      · have hgω : g ω = Real.exp (r * Z s ω) := Set.indicator_of_mem hωA _
        rw [hgω]
        have hy : |r * Δ ω| ≤ 1 := by
          rw [abs_mul, abs_of_pos hr]
          calc r * |Δ ω| ≤ r * (t0 * δmax) := mul_le_mul_of_nonneg_left (hΔb ω) hr.le
            _ = r * t0 * δmax := by ring
            _ ≤ 1 := hrt0le
        have h1 := exp_le_quad hy
        have hsq : (r * Δ ω) ^ 2 ≤ r ^ 2 * ((t0 : ℝ) * δmax) ^ 2 := by
          rw [mul_pow]
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hΔb ω) 2
        have hsplit : Real.exp (r * Z (s + t0) ω) = Real.exp (r * Z s ω) * Real.exp (r * Δ ω) := by
          rw [← Real.exp_add]; congr 1; simp only [hΔ]; ring
        rw [hsplit]
        have hpos := Real.exp_pos (r * Z s ω)
        have hE0 : 0 < E := Real.exp_pos _
        have := mul_le_mul_of_nonneg_left (show Real.exp (r * Δ ω) ≤ c' + r * Δ ω by
          rw [hc']; linarith) hpos.le
        nlinarith
      · have hgω : g ω = 0 := Set.indicator_of_notMem hωA _
        rw [hgω]
        simp only [mul_zero, zero_mul, add_zero]
        rw [hE, Real.exp_le_exp]
        have hlt : Z s ω < θ := by simpa [hA] using hωA
        have := (abs_le.1 (hΔb ω)).2
        simp only [hΔ] at this
        have : Z (s + t0) ω ≤ θ + t0 * δmax := by linarith
        exact mul_le_mul_of_nonneg_left this hr.le
    have hint12 : Integrable (fun ω => E + c' * g ω) μ :=
      (integrable_const E).add (hgint.const_mul c')
    have hint3 : Integrable (fun ω => r * (g * Δ) ω) μ := hgΔint.const_mul r
    have hint_rhs : Integrable (fun ω => E + c' * g ω + r * (g * Δ) ω) μ := hint12.add hint3
    have hmono := integral_mono (hexpint (s + t0)) hint_rhs hpt
    rw [integral_add hint12 hint3,
      integral_add (integrable_const E) (hgint.const_mul c'), integral_const,
      integral_const_mul, integral_const_mul, hkey1] at hmono
    simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
    rw [integral_const_mul] at hkey2
    have hgI : ∫ ω, g ω ∂μ ≤ ∫ ω, Real.exp (r * Z s ω) ∂μ := integral_mono hgint (hexpint s) hgle
    have hgI0 : 0 ≤ ∫ ω, g ω ∂μ := integral_nonneg hg0
    -- c' - r t0 ζ ≤ ρ
    have hcoef : c' - r * (t0 * ζ) ≤ ρ := by
      rw [hc', hρ]
      have e1 : r ^ 2 * ((t0 : ℝ) * δmax) ^ 2 = (ζ / (4 * δmax)) ^ 2 := by
        rw [← hrt0]; ring
      have e2 : r * (t0 * ζ) = ζ ^ 2 / (4 * δmax ^ 2) := by
        rw [hr_def]; field_simp
      rw [e1, e2]
      have : (ζ / (4 * δmax)) ^ 2 = ζ ^ 2 / (16 * δmax ^ 2) := by
        field_simp; ring
      rw [this]
      have h16 : ζ ^ 2 / (16 * δmax ^ 2) + ζ ^ 2 / (8 * δmax ^ 2) ≤ ζ ^ 2 / (4 * δmax ^ 2) := by
        rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith [sq_nonneg ζ, sq_nonneg δmax, mul_pos (pow_pos hζ 2) (pow_pos hδ 2)]
      linarith
    have hcoef0 : 0 ≤ c' - r * (t0 * ζ) ∨ c' - r * (t0 * ζ) < 0 := le_or_gt _ _
    have hfin : c' * ∫ ω, g ω ∂μ + r * ∫ ω, (g * μ[Δ | ℱ s]) ω ∂μ ≤
        ρ * ∫ ω, Real.exp (r * Z s ω) ∂μ := by
      have h1 : r * ∫ ω, (g * μ[Δ | ℱ s]) ω ∂μ ≤ r * (-((t0 : ℝ) * ζ) * ∫ ω, g ω ∂μ) :=
        mul_le_mul_of_nonneg_left hkey2 hr.le
      have h2 : (c' - r * (t0 * ζ)) * ∫ ω, g ω ∂μ ≤ ρ * ∫ ω, g ω ∂μ :=
        mul_le_mul_of_nonneg_right hcoef hgI0
      have h3 : ρ * ∫ ω, g ω ∂μ ≤ ρ * ∫ ω, Real.exp (r * Z s ω) ∂μ :=
        mul_le_mul_of_nonneg_left hgI hρ0
      nlinarith
    linarith
  -- uniform bound on the exponential moment
  have hbound : ∀ t, 1 ≤ t → ∫ ω, Real.exp (r * Z t ω) ∂μ ≤ B := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      by_cases h : t ≤ t0
      · have hpt : ∀ ω, Real.exp (r * Z t ω) ≤ E := by
          intro ω
          rw [hE, Real.exp_le_exp]
          apply mul_le_mul_of_nonneg_left _ hr.le
          have h1 := (abs_le.1 (hZb t ω)).2
          have h2 : (t : ℝ) * δmax ≤ t0 * δmax :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast h) hδ.le
          linarith
        calc ∫ ω, Real.exp (r * Z t ω) ∂μ ≤ ∫ ω, E ∂μ :=
              integral_mono (hexpint t) (integrable_const E) hpt
          _ = E := by simp
          _ ≤ B := hEB
      · push_neg at h
        obtain ⟨s, rfl⟩ : ∃ s, t = s + t0 := ⟨t - t0, by omega⟩
        have hs : 1 ≤ s := by omega
        have h1 := hstep s hs
        have h2 := ih s (by omega) hs
        have h3 : ρ * ∫ ω, Real.exp (r * Z s ω) ∂μ ≤ ρ * B := mul_le_mul_of_nonneg_left h2 hρ0
        have h4 : ρ * B + E = B := by
          rw [hB]; field_simp; ring
        linarith
  -- Jensen
  intro t ht
  set M := ∫ ω, Z t ω ∂μ with hM
  have hZint : Integrable (Z t) μ :=
    Integrable.of_bound (hZm t).aestronglyMeasurable (t * δmax)
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hZb t ω)
  have hJ : Real.exp (r * M) ≤ ∫ ω, Real.exp (r * Z t ω) ∂μ := by
    have hpt : ∀ ω, Real.exp (r * M) * (1 + (r * Z t ω - r * M)) ≤ Real.exp (r * Z t ω) :=
      fun ω => exp_ge_tangent _ _
    have hi2 : Integrable (fun ω => r * Z t ω - r * M) μ :=
      (hZint.const_mul r).sub (integrable_const (r * M))
    have hint : Integrable (fun ω => Real.exp (r * M) * (1 + (r * Z t ω - r * M))) μ :=
      (((integrable_const 1).add hi2)).const_mul _
    have := integral_mono hint (hexpint t) hpt
    rw [integral_const_mul, integral_add (integrable_const 1) hi2,
      integral_sub (hZint.const_mul r) (integrable_const (r * M)), integral_const_mul,
      integral_const, integral_const] at this
    simp only [probReal_univ, smul_eq_mul, one_mul, ← hM, sub_self, add_zero, mul_one] at this
    exact this
  have hBpos : 0 < B := lt_of_lt_of_le (Real.exp_pos _) hEB
  have hlog : r * M ≤ Real.log B := by
    rw [← Real.exp_le_exp, Real.exp_log hBpos]
    exact le_trans hJ (hbound t ht)
  have hlogB : Real.log B = r * (θ + t0 * δmax) + Real.log (8 * δmax ^ 2 / ζ ^ 2) := by
    rw [hB, hρ1, hE, Real.log_div (by positivity) (by positivity), Real.log_exp]
    have : 8 * δmax ^ 2 / ζ ^ 2 = (ζ ^ 2 / (8 * δmax ^ 2))⁻¹ := by rw [inv_div]
    rw [this, Real.log_inv]
    ring
  rw [hlogB] at hlog
  have hinv : (t0 : ℝ) * (4 * δmax ^ 2 / ζ) = 1 / r := by
    rw [hr_def]; field_simp
  rw [hinv]
  have : M ≤ (θ + t0 * δmax) + Real.log (8 * δmax ^ 2 / ζ ^ 2) / r := by
    have : M - (θ + t0 * δmax) ≤ Real.log (8 * δmax ^ 2 / ζ ^ 2) / r := by
      rw [le_div_iff₀ hr]; nlinarith
    linarith
  have e : 1 / r * Real.log (8 * δmax ^ 2 / ζ ^ 2) = Real.log (8 * δmax ^ 2 / ζ ^ 2) / r := by
    ring
  rw [e]
  linarith
