-- Prove2me | solution 1 for ProbMetricStab.Portfolio.nonsingular_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:08:25.439128+00:00
-- url     : https://prove2.me/submissions/bfe884eb-6467-473c-b5eb-4a635f0b25d1

import Mathlib
import Definitions.Def_ProbMetricStab_Portfolio_Setting

open MeasureTheory ProbMetricStab.Portfolio

theorem solution {s : ℕ} (Γ : Measure (Rs s)) (hΓ : IsSpectral Γ)
    (hns : Nonsingular Γ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Rs s,
      c * ‖x‖ ^ 2 ≤ ∫ ξ in unitSphere s, |(inner ℝ x ξ : ℝ)| ^ 2 ∂Γ := by
  letI : IsProbabilityMeasure Γ := hΓ.1
  let Q : Rs s → ℝ := fun x => ∫ ξ in unitSphere s, |(inner ℝ x ξ : ℝ)| ^ 2 ∂Γ
  have hQ : Continuous Q := by
    apply continuous_parametric_integral_of_continuous
    · change Continuous (fun z : Rs s × Rs s => |(inner ℝ z.1 z.2 : ℝ)| ^ 2)
      fun_prop
    · exact isCompact_sphere 0 1
  have hQ0 (x : Rs s) : 0 ≤ Q x := integral_nonneg fun _ => sq_nonneg _
  have hscale (a : ℝ) (x : Rs s) : Q (a • x) = a ^ 2 * Q x := by
    dsimp [Q]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ξ
    simp only [inner_smul_left, conj_trivial, abs_mul, mul_pow, sq_abs]
  by_cases hn : Nontrivial (Rs s)
  · letI := hn
    have hne : (unitSphere s).Nonempty := by
      exact NormedSpace.sphere_nonempty.mpr (by norm_num)
    obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : Rs s) 1).exists_isMinOn hne hQ.continuousOn
    have hnu : ‖u‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hu
    have hpos : 0 < Q u := by
      apply lt_of_le_of_ne (hQ0 u)
      intro he
      have hu0 := hns u he.symm
      simp [hu0] at hnu
    refine ⟨Q u, hpos, ?_⟩
    intro x
    by_cases hx : x = 0
    · simp [hx, Q]
    have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hv : (‖x‖⁻¹ : ℝ) • x ∈ unitSphere s := by
      simp [unitSphere, Metric.mem_sphere, dist_zero_right, norm_smul,
        abs_of_nonneg (inv_nonneg.mpr hnx.le), ne_of_gt hnx]
    have hb := hmin hv
    change Q u ≤ Q ((‖x‖⁻¹ : ℝ) • x) at hb
    rw [hscale] at hb
    have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖x‖)
    field_simp [ne_of_gt hnx] at hm
    nlinarith
  · haveI : Subsingleton (Rs s) := not_nontrivial_iff_subsingleton.mp hn
    refine ⟨1, zero_lt_one, ?_⟩
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]

#print axioms solution
