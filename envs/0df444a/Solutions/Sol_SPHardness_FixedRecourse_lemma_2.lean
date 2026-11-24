-- Prove2me | solution 1 for SPHardness.FixedRecourse.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T00:26:29.951706+00:00
-- url     : https://prove2.me/submissions/14cd1601-b688-4e5b-87c6-f37bafc51b20

import Mathlib
import Definitions.Def_SPHardness_FixedRecourse_Model

noncomputable section
open MeasureTheory
open scoped BigOperators

open SPHardness.FixedRecourse

namespace L2Aux

def gs {k : ℕ} (α : Fin k → ℝ) (ξ : Fin k → ℝ) : ℝ := ∑ j, α j * ξ j

lemma cube_vol (m : ℕ) : volume (cube m) = 1 := by
  rw [cube, volume_pi_pi]
  simp

lemma cube_meas (m : ℕ) : MeasurableSet (cube m) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

lemma gs_cont {k : ℕ} (α : Fin k → ℝ) : Continuous (gs α) :=
  continuous_finset_sum _ (fun j _ => continuous_const.mul (continuous_apply j))

lemma sec {k : ℕ} (α : Fin k → ℝ) (hα : ∀ j, 0 ≤ α j) (t : ℝ) (ξ : Fin k → ℝ)
    (hξ : ξ ∈ cube k) : secondStageValue α t ξ = max 0 (gs α ξ - t) := by
  have hξ0 : ∀ j, 0 ≤ ξ j := fun j => (hξ j (Set.mem_univ j)).1
  unfold secondStageValue
  apply IsGreatest.csSup_eq
  constructor
  · rcases le_total 0 (gs α ξ - t) with h | h
    · rw [max_eq_right h]
      refine ⟨α, 1, hα, fun j => by rw [mul_one], zero_le_one, le_refl _, ?_⟩
      unfold gs
      rw [mul_one]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    · rw [max_eq_left h]
      exact ⟨0, 0, fun _ => le_refl 0, fun j => by simp, le_refl 0, zero_le_one, by simp⟩
  · rintro v ⟨y, z, hy0, hyz, hz0, hz1, rfl⟩
    have h1 : ∑ j, ξ j * y j ≤ z * gs α ξ := by
      unfold gs
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      calc ξ j * y j ≤ ξ j * (α j * z) := mul_le_mul_of_nonneg_left (hyz j) (hξ0 j)
        _ = z * (α j * ξ j) := by ring
    have h2 : z * gs α ξ - t * z ≤ max 0 (gs α ξ - t) := by
      rcases le_total 0 (gs α ξ - t) with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h]; nlinarith
    linarith

lemma key (x β h : ℝ) :
    |max 0 (x - (β + h)) - max 0 (x - β) + h * Set.indicator (Set.Ioi β) (fun _ => (1 : ℝ)) x| ≤
      |h| * Set.indicator (Set.Icc (β - |h|) (β + |h|)) (fun _ => (1 : ℝ)) x := by
  rcases le_or_gt x β with hu | hu
  · have hn : x ∉ Set.Ioi β := not_lt.mpr hu
    simp only [Set.indicator_of_notMem hn, mul_zero, add_zero]
    rw [max_eq_left (by linarith : x - β ≤ 0), sub_zero]
    rcases le_total 0 (x - (β + h)) with h1 | h1
    · have hh : h ≤ 0 := by linarith
      have hm : x ∈ Set.Icc (β - |h|) (β + |h|) := by
        rw [abs_of_nonpos hh]; exact ⟨by linarith, by linarith⟩
      simp only [Set.indicator_of_mem hm, mul_one]
      rw [max_eq_right h1, abs_of_nonpos hh, abs_le]
      constructor <;> linarith
    · rw [max_eq_left h1, abs_zero]
      exact mul_nonneg (abs_nonneg h) (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
  · have hm0 : x ∈ Set.Ioi β := hu
    simp only [Set.indicator_of_mem hm0, mul_one]
    rw [max_eq_right (by linarith : 0 ≤ x - β)]
    rcases le_total 0 (x - (β + h)) with h1 | h1
    · rw [max_eq_right h1, show x - (β + h) - (x - β) + h = 0 by ring, abs_zero]
      exact mul_nonneg (abs_nonneg h) (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
    · have hh : 0 < h := by linarith
      have hm : x ∈ Set.Icc (β - |h|) (β + |h|) := by
        rw [abs_of_pos hh]; exact ⟨by linarith, by linarith⟩
      simp only [Set.indicator_of_mem hm, mul_one]
      rw [max_eq_left h1, abs_of_pos hh, abs_le]
      constructor <;> linarith

lemma slab {n : ℕ} (α : Fin (n + 1) → ℝ) (j0 : Fin (n + 1)) (ha : 0 < α j0) (lo hi : ℝ) :
    volume {ξ : Fin (n + 1) → ℝ | ξ ∈ cube (n + 1) ∧ lo ≤ gs α ξ ∧ gs α ξ ≤ hi} ≤
      ENNReal.ofReal ((hi - lo) / α j0) := by
  set a := α j0 with ha_def
  let c : (Fin n → ℝ) → ℝ := fun y => ∑ j : Fin n, α (j0.succAbove j) * y j
  let E : Set (ℝ × (Fin n → ℝ)) :=
    {p | p.2 ∈ cube n ∧ lo ≤ a * p.1 + c p.2 ∧ a * p.1 + c p.2 ≤ hi}
  have memE : ∀ x y, (x, y) ∈ E ↔ (y ∈ cube n ∧ lo ≤ a * x + c y ∧ a * x + c y ≤ hi) :=
    fun _ _ => Iff.rfl
  have hc_meas : Measurable c := by
    show Measurable (fun y : Fin n → ℝ => ∑ j : Fin n, α (j0.succAbove j) * y j)
    fun_prop
  have hf : Measurable (fun p : ℝ × (Fin n → ℝ) => a * p.1 + c p.2) :=
    (measurable_const.mul measurable_fst).add (hc_meas.comp measurable_snd)
  have hE : MeasurableSet E :=
    (measurable_snd (cube_meas n)).inter
      ((measurableSet_le measurable_const hf).inter (measurableSet_le hf measurable_const))
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j0
  have hsub : {ξ : Fin (n + 1) → ℝ | ξ ∈ cube (n + 1) ∧ lo ≤ gs α ξ ∧ gs α ξ ≤ hi} ⊆
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j0) ⁻¹' E := by
    rintro ξ ⟨hcube', h1, h2⟩
    have hsplit : gs α ξ = a * ξ j0 +
        ∑ j : Fin n, α (j0.succAbove j) * ξ (j0.succAbove j) :=
      Fin.sum_univ_succAbove _ j0
    show (fun j => ξ (j0.succAbove j)) ∈ cube n ∧
      lo ≤ a * ξ j0 + ∑ j : Fin n, α (j0.succAbove j) * ξ (j0.succAbove j) ∧
      a * ξ j0 + ∑ j : Fin n, α (j0.succAbove j) * ξ (j0.succAbove j) ≤ hi
    refine ⟨fun j _ => hcube' _ (Set.mem_univ _), ?_, ?_⟩
    · linarith
    · linarith
  calc volume {ξ : Fin (n + 1) → ℝ | ξ ∈ cube (n + 1) ∧ lo ≤ gs α ξ ∧ gs α ξ ≤ hi}
      ≤ volume ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j0) ⁻¹' E) :=
        measure_mono hsub
    _ = (volume : Measure (ℝ × (Fin n → ℝ))) E := hmp.measure_preimage hE.nullMeasurableSet
    _ = ∫⁻ y, volume ((fun x => (x, y)) ⁻¹' E) ∂(volume : Measure (Fin n → ℝ)) := by
        rw [Measure.volume_eq_prod]
        exact Measure.prod_apply_symm hE
    _ ≤ ∫⁻ y, (cube n).indicator (fun _ => ENNReal.ofReal ((hi - lo) / a)) y
          ∂(volume : Measure (Fin n → ℝ)) := by
        apply lintegral_mono
        intro y
        by_cases hy : y ∈ cube n
        · rw [Set.indicator_of_mem hy]
          calc volume ((fun x => (x, y)) ⁻¹' E)
              ≤ volume (Set.Icc ((lo - c y) / a) ((hi - c y) / a)) := by
                apply measure_mono
                intro x hx
                obtain ⟨_, h1, h2⟩ := (memE x y).mp hx
                constructor
                · rw [div_le_iff₀ ha]; linarith
                · rw [le_div_iff₀ ha]; linarith
            _ = ENNReal.ofReal ((hi - lo) / a) := by
                rw [Real.volume_Icc]
                congr 1
                ring
        · rw [Set.indicator_of_notMem hy]
          exact (measure_mono_null (fun x hx => (hy ((memE x y).mp hx).1).elim)
            measure_empty).le
    _ = ENNReal.ofReal ((hi - lo) / a) * volume (cube n) := lintegral_indicator_const (cube_meas n) _
    _ = ENNReal.ofReal ((hi - lo) / a) := by rw [cube_vol, mul_one]

end L2Aux

open L2Aux

theorem solution {k : ℕ} (α : Fin k → ℝ) (β : ℝ)
    (hα : ∀ j, 0 ≤ α j) (hβ : 0 ≤ β)
    (hnontrivial : (∃ j, 0 < α j) ∨ 0 < β) :
    HasDerivAt (fun t => expRecourse α t) (vol α β - 1) β := by
  classical
  have hF : ∀ t, expRecourse α t = ∫ ξ in cube k, max 0 (gs α ξ - t) := fun t =>
    setIntegral_congr_fun (cube_meas k) (fun ξ hξ => sec α hα t ξ hξ)
  by_cases hex : ∃ j, 0 < α j
  · obtain ⟨j0, hj0⟩ := hex
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := j0.pos; omega⟩
    have hGc := gs_cont α
    have hGm : Measurable (gs α) := hGc.measurable
    haveI : IsFiniteMeasure (volume.restrict (cube (n + 1))) :=
      isFiniteMeasure_restrict.mpr (by rw [cube_vol]; exact ENNReal.one_ne_top)
    have hcomp : IsCompact (cube (n + 1)) := isCompact_univ_pi (fun _ => isCompact_Icc)
    have hint : ∀ t, Integrable (fun ξ => max 0 (gs α ξ - t)) (volume.restrict (cube (n + 1))) :=
      fun t => (continuous_const.max (hGc.sub continuous_const)).continuousOn.integrableOn_compact
        hcomp
    have hind : ∀ s : Set ℝ, MeasurableSet s →
        Integrable (fun ξ => s.indicator (fun _ => (1 : ℝ)) (gs α ξ))
          (volume.restrict (cube (n + 1))) := by
      intro s hs
      refine Integrable.mono' (integrable_const (1 : ℝ))
        ((measurable_const.indicator hs).comp hGm).aestronglyMeasurable (ae_of_all _ (fun ξ => ?_))
      rw [Real.norm_eq_abs]
      by_cases hx : gs α ξ ∈ s
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    have hindint : ∀ s : Set ℝ, MeasurableSet s →
        ∫ ξ in cube (n + 1), s.indicator (fun _ => (1 : ℝ)) (gs α ξ) =
          (volume (gs α ⁻¹' s ∩ cube (n + 1))).toReal := by
      intro s hs
      have : (fun ξ => s.indicator (fun _ => (1 : ℝ)) (gs α ξ)) =
          (gs α ⁻¹' s).indicator (fun _ => (1 : ℝ)) := by
        funext ξ; rfl
      rw [this, integral_indicator_const _ (hGm hs), smul_eq_mul, mul_one, measureReal_def,
        Measure.restrict_apply (hGm hs)]
    set D := -∫ ξ in cube (n + 1), (Set.Ioi β).indicator (fun _ => (1 : ℝ)) (gs α ξ) with hD
    have hDV : D = vol α β - 1 := by
      rw [hD, hindint _ measurableSet_Ioi]
      have hmt : MeasurableSet {ξ : Fin (n + 1) → ℝ | gs α ξ ≤ β} :=
        measurableSet_le hGm measurable_const
      have hsum := measure_inter_add_diff (μ := volume) (cube (n + 1)) hmt
      have e1 : cube (n + 1) ∩ {ξ | gs α ξ ≤ β} = knapsack α β := rfl
      have e2 : cube (n + 1) \ {ξ | gs α ξ ≤ β} = gs α ⁻¹' Set.Ioi β ∩ cube (n + 1) := by
        ext ξ
        simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_Ioi, not_le]
        exact and_comm
      rw [e1, e2, cube_vol] at hsum
      have hf1 : volume (knapsack α β) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top
          (by rw [← cube_vol (n + 1)]; exact measure_mono (fun ξ hξ => hξ.1))
      have hf2 : volume (gs α ⁻¹' Set.Ioi β ∩ cube (n + 1)) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top
          (by rw [← cube_vol (n + 1)]; exact measure_mono (fun ξ hξ => hξ.2))
      have h3 := congrArg ENNReal.toReal hsum
      rw [ENNReal.toReal_add hf1 hf2, ENNReal.toReal_one] at h3
      unfold vol
      linarith
    have hderiv : HasDerivAt (fun t => ∫ ξ in cube (n + 1), max 0 (gs α ξ - t)) D β := by
      rw [hasDerivAt_iff_isLittleO_nhds_zero]
      have bound : ∀ h : ℝ, ‖(∫ ξ in cube (n + 1), max 0 (gs α ξ - (β + h))) -
          (∫ ξ in cube (n + 1), max 0 (gs α ξ - β)) - h • D‖ ≤ (2 / α j0) * ‖h ^ 2‖ := by
        intro h
        have hexp : (∫ ξ in cube (n + 1), max 0 (gs α ξ - (β + h))) -
            (∫ ξ in cube (n + 1), max 0 (gs α ξ - β)) - h • D =
            ∫ ξ in cube (n + 1), (max 0 (gs α ξ - (β + h)) - max 0 (gs α ξ - β) +
              h * (Set.Ioi β).indicator (fun _ => (1 : ℝ)) (gs α ξ)) := by
          rw [integral_add (show Integrable (fun ξ => max 0 (gs α ξ - (β + h)) - max 0 (gs α ξ - β))
              (volume.restrict (cube (n + 1))) from (hint _).sub (hint _))
              ((hind _ measurableSet_Ioi).const_mul h),
            integral_sub (hint _) (hint _), integral_const_mul, hD, smul_eq_mul]
          ring
        rw [hexp]
        have hIcc := hind (Set.Icc (β - |h|) (β + |h|)) measurableSet_Icc
        calc ‖∫ ξ in cube (n + 1), (max 0 (gs α ξ - (β + h)) - max 0 (gs α ξ - β) +
              h * (Set.Ioi β).indicator (fun _ => (1 : ℝ)) (gs α ξ))‖
            ≤ ∫ ξ in cube (n + 1),
                |h| * (Set.Icc (β - |h|) (β + |h|)).indicator (fun _ => (1 : ℝ)) (gs α ξ) :=
              norm_integral_le_of_norm_le (hIcc.const_mul _)
                (ae_of_all _ (fun ξ => by rw [Real.norm_eq_abs]; exact key (gs α ξ) β h))
          _ = |h| * (volume (gs α ⁻¹' Set.Icc (β - |h|) (β + |h|) ∩ cube (n + 1))).toReal := by
              rw [integral_const_mul, hindint _ measurableSet_Icc]
          _ ≤ |h| * (2 * |h| / α j0) := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg h)
              have hs := slab α j0 hj0 (β - |h|) (β + |h|)
              rw [show β + |h| - (β - |h|) = 2 * |h| by ring] at hs
              apply ENNReal.toReal_le_of_le_ofReal (div_nonneg (by linarith [abs_nonneg h]) hj0.le)
              refine le_trans (measure_mono ?_) hs
              rintro ξ ⟨h1, h2⟩
              exact ⟨h2, h1.1, h1.2⟩
          _ = (2 / α j0) * ‖h ^ 2‖ := by
              rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h), ← sq_abs h]
              ring
      exact (Asymptotics.IsBigO.of_bound (2 / α j0) (Filter.Eventually.of_forall bound)).trans_isLittleO
        (Asymptotics.isLittleO_pow_id one_lt_two)
    have hfun : (fun t => expRecourse α t) = fun t => ∫ ξ in cube (n + 1), max 0 (gs α ξ - t) :=
      funext hF
    rw [hfun, ← hDV]
    exact hderiv
  · have hβpos : 0 < β := hnontrivial.resolve_left hex
    have hα0 : ∀ j, α j = 0 := fun j => le_antisymm (not_lt.mp (fun h => hex ⟨j, h⟩)) (hα j)
    have hg0 : ∀ ξ, gs α ξ = 0 := fun ξ =>
      Finset.sum_eq_zero (fun j _ => by rw [hα0 j, zero_mul])
    have hV : vol α β = 1 := by
      unfold vol
      have hK : knapsack α β = cube k := by
        ext ξ
        constructor
        · exact fun h => h.1
        · intro h
          refine ⟨h, ?_⟩
          have := hg0 ξ
          unfold gs at this
          linarith
      rw [hK, cube_vol]
      simp
    rw [hV, sub_self]
    apply (hasDerivAt_const β (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hβpos] with t ht
    show expRecourse α t = 0
    rw [hF t]
    have ht' : 0 < t := ht
    have hz : (fun ξ => max 0 (gs α ξ - t)) = fun _ => (0 : ℝ) :=
      funext (fun ξ => by rw [hg0]; exact max_eq_left (by linarith))
    rw [hz]
    simp
