-- Prove2me | solution 1 for SustainableFashion.Variety.expected_price
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:09:47.768084+00:00
-- url     : https://prove2.me/submissions/2588d8d2-c1d6-4418-87fa-c7ae44a88f97

import Mathlib
import Definitions.Def_SustainableFashion_Variety_Setting

set_option autoImplicit false
open MeasureTheory SustainableFashion.Variety

noncomputable def gg (y : ℝ) : ℝ := |y - round y|

lemma gg_eq_norm (y : ℝ) : gg y = ‖(y : UnitAddCircle)‖ := by
  unfold gg
  exact (UnitAddCircle.norm_eq).symm

lemma gg_cont : Continuous gg := by
  have : gg = fun y : ℝ => ‖(y : UnitAddCircle)‖ := funext gg_eq_norm
  rw [this]
  exact continuous_norm.comp (AddCircle.continuous_mk' 1)

lemma gg_periodic : Function.Periodic gg 1 := by
  intro y
  unfold gg
  rw [round_add_one]
  push_cast
  congr 1
  ring

lemma gg_unit : ∫ y in (0 : ℝ)..1, gg y = 1 / 4 := by
  have h : ∀ y ∈ Set.uIcc (0 : ℝ) 1, gg y = min y (1 - y) := by
    intro y hy
    rw [Set.uIcc_of_le zero_le_one] at hy
    obtain ⟨h0, h1⟩ := hy
    unfold gg
    by_cases hh : y < 1 / 2
    · have : round y = 0 := by
        rw [round_eq, Int.floor_eq_iff]
        constructor <;> push_cast <;> linarith
      rw [this, min_eq_left (by linarith)]
      simp [abs_of_nonneg h0]
    · push_neg at hh
      have : round y = 1 := by
        rw [round_eq, Int.floor_eq_iff]
        constructor <;> push_cast <;> linarith
      rw [this, min_eq_right (by linarith)]
      push_cast
      rw [abs_of_nonpos (by linarith)]
      ring
  rw [intervalIntegral.integral_congr h]
  have hc : Continuous (fun y : ℝ => min y (1 - y)) := continuous_id.min (continuous_const.sub continuous_id)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have e1 : ∫ y in (0 : ℝ)..1 / 2, min y (1 - y) = ∫ y in (0 : ℝ)..1 / 2, y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le (by norm_num)] at hy
    exact min_eq_left (by linarith [hy.2])
  have e2 : ∫ y in (1 / 2 : ℝ)..1, min y (1 - y) = ∫ y in (1 / 2 : ℝ)..1, (1 - y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le (by norm_num)] at hy
    exact min_eq_right (by linarith [hy.1])
  rw [e1, e2, integral_id, intervalIntegral.integral_sub (by simp) (by exact intervalIntegral.intervalIntegrable_id)]
  simp only [integral_id, intervalIntegral.integral_const, smul_eq_mul]
  norm_num

lemma gg_int (m : ℕ) : ∫ y in (0 : ℝ)..m, gg y = m / 4 := by
  have h1 : ∀ k < m, IntervalIntegrable gg MeasureTheory.volume ((fun k : ℕ => (k : ℝ)) k)
      ((fun k : ℕ => (k : ℝ)) (k + 1)) := fun k _ => gg_cont.intervalIntegrable _ _
  have := intervalIntegral.sum_integral_adjacent_intervals (f := gg) (μ := MeasureTheory.volume)
    (a := fun k : ℕ => (k : ℝ)) (n := m) h1
  simp only [Nat.cast_zero] at this
  rw [← this]
  have hk : ∀ k ∈ Finset.range m, ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ), gg x = 1 / 4 := by
    intro k _
    have := gg_periodic.intervalIntegral_add_eq (k : ℝ) 0
    push_cast
    rw [this, zero_add]
    exact gg_unit
  rw [Finset.sum_congr rfl hk]
  simp
  ring

lemma nd_eq (m : ℕ) [NeZero m] (x : ℝ) :
    nearestDist (equalSpacing m) (x : UnitAddCircle) = gg (m * x) / m := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
  have hm' : (m : ℝ) ≠ 0 := hm.ne'
  have key : ∀ i : Fin m, dist (equalSpacing m i) (x : UnitAddCircle) =
      |((i : ℕ) : ℝ) / m - x - round (((i : ℕ) : ℝ) / m - x)| := by
    intro i
    unfold equalSpacing
    rw [dist_eq_norm, ← AddCircle.coe_sub]
    exact UnitAddCircle.norm_eq
  apply le_antisymm
  · set r : ℤ := round ((m : ℝ) * x) with hr
    have h1 : 0 ≤ r % (m : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hm')
    have h2 : r % (m : ℤ) < m := Int.emod_lt_of_pos _ (by exact_mod_cast hm)
    let i₀ : Fin m := ⟨(r % (m : ℤ)).toNat, by omega⟩
    have hi₀ : ((i₀ : ℕ) : ℤ) = r % (m : ℤ) := by
      show (((r % (m : ℤ)).toNat : ℕ) : ℤ) = _
      exact Int.toNat_of_nonneg h1
    refine (Finset.inf'_le _ (Finset.mem_univ i₀)).trans ?_
    rw [key i₀]
    refine (round_le _ (-(r / (m : ℤ)))).trans ?_
    have hdec : (r : ℝ) = ((i₀ : ℕ) : ℝ) + m * ((r / (m : ℤ) : ℤ) : ℝ) := by
      have := Int.emod_add_mul_ediv r (m : ℤ)
      have h3 : ((i₀ : ℕ) : ℤ) + (m : ℤ) * (r / (m : ℤ)) = r := by rw [hi₀]; exact this
      exact_mod_cast h3.symm
    unfold gg
    have : ((i₀ : ℕ) : ℝ) / m - x - ((-(r / (m : ℤ)) : ℤ) : ℝ) = (r - m * x) / m := by
      push_cast
      rw [hdec]
      field_simp
      ring
    rw [this, abs_div, abs_of_pos hm, abs_sub_comm]
  · apply Finset.le_inf'
    intro i _
    rw [key i]
    set z : ℝ := ((i : ℕ) : ℝ) / m - x with hz
    have hz' : z - round z = (((i : ℕ) : ℝ) - m * round z - m * x) / m := by
      rw [hz]; field_simp; ring
    rw [hz']
    rw [abs_div, abs_of_pos hm]
    apply div_le_div_of_nonneg_right _ hm.le
    unfold gg
    have := round_le ((m : ℝ) * x) ((i : ℤ) - m * round z)
    push_cast at this
    calc |(m : ℝ) * x - round ((m : ℝ) * x)| ≤ |(m : ℝ) * x - (((i : ℕ) : ℝ) - m * round z)| := this
      _ = |(((i : ℕ) : ℝ) - m * round z - m * x)| := abs_sub_comm _ _

theorem solution (m : ℕ) [NeZero m] (a θ γ u : ℝ) :
    expNearestDist (equalSpacing m) = 1 / (4 * m) ∧
    ∫ x, (a + θ * u + γ / 2 - γ * nearestDist (equalSpacing m) x) =
      a + θ * u + γ / 2 - γ / (4 * m) := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
  have hE : expNearestDist (equalSpacing m) = 1 / (4 * m) := by
    unfold expNearestDist
    rw [← UnitAddCircle.intervalIntegral_preimage 0 (nearestDist (equalSpacing m))]
    simp only [zero_add]
    have : ∫ x in (0 : ℝ)..1, nearestDist (equalSpacing m) (x : UnitAddCircle) =
        ∫ x in (0 : ℝ)..1, gg (m * x) / m := by
      apply intervalIntegral.integral_congr
      intro x _
      exact nd_eq m x
    rw [this, intervalIntegral.integral_div, intervalIntegral.integral_comp_mul_left (fun y => gg y) hm.ne']
    simp only [mul_zero, mul_one, smul_eq_mul]
    rw [gg_int]
    field_simp
  refine ⟨hE, ?_⟩
  have hcont : Continuous (nearestDist (equalSpacing m)) := by
    unfold nearestDist
    exact Continuous.finset_inf'_apply _ (fun i _ => continuous_const.dist continuous_id)
  have hint : Integrable (nearestDist (equalSpacing m)) := by
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hvol : (volume : Measure UnitAddCircle) Set.univ = 1 := by
    rw [AddCircle.measure_univ]; simp
  rw [integral_sub (integrable_const _) (hint.const_mul γ), integral_const, integral_const_mul]
  have : (volume : Measure UnitAddCircle).real Set.univ = 1 := by
    simp [Measure.real, hvol]
  rw [this]
  have h2 : ∫ x, nearestDist (equalSpacing m) x = 1 / (4 * m) := hE
  rw [h2]
  simp
  ring
