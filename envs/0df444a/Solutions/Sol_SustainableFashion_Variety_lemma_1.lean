-- Prove2me | solution 1 for SustainableFashion.Variety.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:12:09.007675+00:00
-- url     : https://prove2.me/submissions/8ea5f9a8-f2e6-41e7-a32d-33cd560ec903

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

lemma expE (m : ℕ) [NeZero m] : expNearestDist (equalSpacing m) = 1 / (4 * m) := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
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

lemma lower (m : ℕ) [NeZero m] (t : Fin m → UnitAddCircle) :
    1 / (4 * (m : ℝ)) ≤ expNearestDist t := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
  unfold expNearestDist
  have hcont : Continuous (nearestDist t) := by
    unfold nearestDist
    exact Continuous.finset_inf'_apply _ (fun i _ => continuous_const.dist continuous_id)
  have hint : Integrable (nearestDist t) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnn : ∀ x, 0 ≤ nearestDist t x := fun x => by
    unfold nearestDist
    exact Finset.le_inf' _ _ (fun i _ => dist_nonneg)
  have hlay := lintegral_eq_lintegral_meas_lt (volume : Measure UnitAddCircle)
    (Filter.Eventually.of_forall hnn) hcont.aemeasurable
  have hpt : ∀ r : ℝ, 0 < r → r ≤ 1 / (2 * m) →
      ENNReal.ofReal (1 - 2 * m * r) ≤ volume {a | r < nearestDist t a} := by
    intro r hr hr2
    have hsub : {a | nearestDist t a ≤ r} ⊆ ⋃ i, Metric.closedBall (t i) r := by
      intro a ha
      simp only [Set.mem_setOf_eq, nearestDist, Finset.inf'_le_iff] at ha
      obtain ⟨i, _, hi⟩ := ha
      exact Set.mem_iUnion.mpr ⟨i, by rw [Metric.mem_closedBall, dist_comm]; exact hi⟩
    have h1 : volume {a | nearestDist t a ≤ r} ≤ ENNReal.ofReal (2 * m * r) := by
      calc volume {a | nearestDist t a ≤ r} ≤ volume (⋃ i, Metric.closedBall (t i) r) :=
            measure_mono hsub
        _ ≤ ∑ i, volume (Metric.closedBall (t i) r) := measure_iUnion_fintype_le _ _
        _ = ∑ i : Fin m, ENNReal.ofReal (min 1 (2 * r)) := by
            simp [AddCircle.volume_closedBall]
        _ ≤ ∑ i : Fin m, ENNReal.ofReal (2 * r) :=
            Finset.sum_le_sum (fun i _ => ENNReal.ofReal_le_ofReal (min_le_right _ _))
        _ = ENNReal.ofReal (2 * m * r) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
            ring_nf
    have hmeas : MeasurableSet {a | nearestDist t a ≤ r} :=
      (isClosed_le hcont continuous_const).measurableSet
    have hcompl : {a | r < nearestDist t a} = {a | nearestDist t a ≤ r}ᶜ := by
      ext a; simp
    have hvol : (volume : Measure UnitAddCircle) Set.univ = 1 := by
      rw [AddCircle.measure_univ]; simp
    rw [hcompl, measure_compl hmeas (measure_ne_top _ _), hvol]
    have h2 : 0 ≤ 2 * (m : ℝ) * r := by positivity
    have h3 : ENNReal.ofReal (1 - 2 * m * r) = 1 - ENNReal.ofReal (2 * m * r) := by
      rw [ENNReal.ofReal_sub _ h2]; simp
    rw [h3]
    exact tsub_le_tsub_left h1 1
  have hIoc : ∫ r in Set.Ioc (0 : ℝ) (1 / (2 * m)), (1 - 2 * m * r) = 1 / (4 * m) := by
    rw [← intervalIntegral.integral_of_le (by positivity)]
    have e1 : ∫ r in (0 : ℝ)..1 / (2 * m), (2 * (m : ℝ) * r) = 1 / (4 * m) := by
      have := intervalIntegral.integral_const_mul (a := (0 : ℝ)) (b := 1 / (2 * m)) (μ := volume)
        (2 * (m : ℝ)) (fun r : ℝ => r)
      rw [this, integral_id]
      field_simp
      ring
    rw [intervalIntegral.integral_sub (by simp) (by apply Continuous.intervalIntegrable; fun_prop), e1]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    field_simp
    ring
  have hge : ENNReal.ofReal (1 / (4 * (m : ℝ))) ≤
      ∫⁻ r in Set.Ioi (0 : ℝ), volume {a | r < nearestDist t a} := by
    calc ENNReal.ofReal (1 / (4 * (m : ℝ)))
        = ENNReal.ofReal (∫ r in Set.Ioc (0 : ℝ) (1 / (2 * m)), (1 - 2 * m * r)) := by rw [hIoc]
      _ = ∫⁻ r in Set.Ioc (0 : ℝ) (1 / (2 * m)), ENNReal.ofReal (1 - 2 * m * r) := by
          apply ofReal_integral_eq_lintegral_ofReal
          · exact (Continuous.integrableOn_Ioc (by fun_prop))
          · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
            have := hr.2
            have h4 : (2 * (m : ℝ)) * r ≤ 1 := by
              calc 2 * (m : ℝ) * r ≤ 2 * m * (1 / (2 * m)) := by gcongr
                _ = 1 := by field_simp
            simp only [Pi.zero_apply]
            linarith
      _ ≤ ∫⁻ r in Set.Ioc (0 : ℝ) (1 / (2 * m)), volume {a | r < nearestDist t a} :=
          setLIntegral_mono' measurableSet_Ioc (fun r hr => hpt r hr.1 hr.2)
      _ ≤ ∫⁻ r in Set.Ioi (0 : ℝ), volume {a | r < nearestDist t a} :=
          lintegral_mono_set Set.Ioc_subset_Ioi_self
  have hL : ∫⁻ x, ENNReal.ofReal (nearestDist t x) = ENNReal.ofReal (∫ x, nearestDist t x) :=
    (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)).symm
  rw [hL] at hlay
  rw [← hlay] at hge
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hnn)).mp hge

theorem solution (m : ℕ) [NeZero m] (t : Fin m → SustainableFashion.Variety.Circle) :
    expNearestDist (equalSpacing m) ≤ expNearestDist t := by
  rw [expE]
  exact lower m t
