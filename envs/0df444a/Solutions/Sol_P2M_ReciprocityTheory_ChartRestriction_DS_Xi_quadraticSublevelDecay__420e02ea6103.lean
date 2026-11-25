-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_quadraticSublevelDecay__420e02ea6103
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:43:27.909135+00:00
-- url     : https://prove2.me/submissions/2b6051c6-9371-4d53-be81-e83afc0a31d9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_PolynomialGrowthIntegrals
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_subgroupData_lagrange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_subgroupData_E_closed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_subgroupData_sublevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open subgroupData
namespace ReciprocityTheory.ChartRestriction.DS.Xi
theorem _root_.solution : SUB := by
  intro δ hδ0 hδ1
  refine ⟨22, ?_⟩
  intro c
  set M := ‖c‖ with hMd
  have hM0 : 0 ≤ M := norm_nonneg _
  have hint : ∀ t : ℝ, (1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ) ≤ 1 := fun t =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg (c 0 + c 1 * t + c 2 * t ^ 2)])
      (by linarith)
  by_cases hM : M ≤ 1
  · calc (∫⁻ t in Icc (1:ℝ) 2, ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)))
        ≤ ∫⁻ t in Icc (1:ℝ) 2, 1 :=
          setLIntegral_mono' measurableSet_Icc (fun t _ => ENNReal.ofReal_le_one.mpr (hint t))
      _ = 1 := by rw [setLIntegral_const, Real.volume_Icc]; norm_num
      _ ≤ ENNReal.ofReal (22 * (1 + M) ^ (-δ / 2)) := by
          rw [← ENNReal.ofReal_one]; apply ENNReal.ofReal_le_ofReal
          have : (2:ℝ) ^ (-1:ℝ) ≤ (1 + M) ^ (-δ / 2) := by
            calc (2:ℝ) ^ (-1:ℝ) ≤ 2 ^ (-δ / 2) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ ≤ (1 + M) ^ (-δ / 2) := Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
          have h2 : (2:ℝ) ^ (-1:ℝ) = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
          linarith
  push Not at hM
  set s := M ^ ((1:ℝ) / 4) with hs
  have hs0 : 0 < s := by positivity
  have hs4 : s ^ 4 = M := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hM0]; norm_num
  have hs1 : 1 < s := by
    by_contra h; push Not at h
    have : s ^ 4 ≤ 1 := pow_le_one₀ hs0.le h
    linarith
  set E := {t | t ∈ Icc (1:ℝ) 2 ∧ ‖qv c t‖ ≤ s ^ 2} with hE
  have hvol : volume E ≤ ENNReal.ofReal (2 * (5 / s)) := by
    apply sublevel c (by positivity)
    intro t1 t2 t3 h1 h3 h12 h23 p1 p2 p3
    have hl := lagrange c (by positivity) h1 h3 h12 h23 p1 p2 p3
    have e : 12 * s ^ 2 / (5 / s) ^ 2 = 12 * s ^ 4 / 25 := by field_simp; ring
    rw [e, hs4] at hl
    linarith
  have hEm : MeasurableSet E := (E_closed c _).measurableSet
  set K := (1 + s ^ 2) ^ (-δ) with hK
  have pw : ∀ t ∈ Icc (1:ℝ) 2, ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)) ≤
      E.indicator 1 t + ENNReal.ofReal K := by
    intro t ht
    by_cases hp : ‖qv c t‖ ≤ s ^ 2
    · have htE : t ∈ E := ⟨ht, hp⟩
      rw [indicator_of_mem htE]
      exact le_trans (ENNReal.ofReal_le_one.mpr (hint t)) le_self_add
    · refine le_trans ?_ le_add_self
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by
        have : s ^ 2 < ‖qv c t‖ := not_le.mp hp
        simp only [qv] at this; linarith) (by linarith)
  have hfin : 2 * (5 / s) + K ≤ 22 * (1 + M) ^ (-δ / 2) := by
    have hA : K ≤ (1 + M) ^ (-δ / 2) := by
      have e : K = ((1 + s ^ 2) ^ 2) ^ (-δ / 2) := by
        rw [hK, ← Real.rpow_natCast (1 + s ^ 2) 2, ← Real.rpow_mul (by positivity)]; congr 1; push_cast; ring
      rw [e]
      exact Real.rpow_le_rpow_of_nonpos (by linarith) (by rw [← hs4]; nlinarith) (by linarith)
    have hB : 1 / (2 * s) ≤ (1 + M) ^ (-δ / 2) := by
      calc 1 / (2 * s) ≤ (1 + s)⁻¹ := by
            rw [one_div]; exact inv_anti₀ (by positivity) (by linarith)
        _ = ((1 + s) ^ 4) ^ (-(1:ℝ) / 4) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_neg_one]; norm_num
        _ ≤ (1 + M) ^ (-(1:ℝ) / 4) := by
            apply Real.rpow_le_rpow_of_nonpos (by linarith) _ (by norm_num)
            rw [← hs4]; nlinarith [pow_pos hs0 3]
        _ ≤ (1 + M) ^ (-δ / 2) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have e2 : 2 * (5 / s) = 20 * (1 / (2 * s)) := by field_simp; ring
    have hX : 0 ≤ (1 + M) ^ (-δ / 2) := by positivity
    rw [e2]; linarith
  calc (∫⁻ t in Icc (1:ℝ) 2, ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)))
      ≤ ∫⁻ t in Icc (1:ℝ) 2, (E.indicator 1 t + ENNReal.ofReal K) := setLIntegral_mono' measurableSet_Icc pw
    _ = (∫⁻ t in Icc (1:ℝ) 2, E.indicator 1 t) + ∫⁻ _ in Icc (1:ℝ) 2, ENNReal.ofReal K :=
        lintegral_add_right _ measurable_const
    _ ≤ volume E + ENNReal.ofReal K := by
        gcongr
        · calc (∫⁻ t in Icc (1:ℝ) 2, E.indicator 1 t) ≤ ∫⁻ t, E.indicator 1 t := setLIntegral_le_lintegral _ _
            _ = volume E := lintegral_indicator_one hEm
        · rw [setLIntegral_const, Real.volume_Icc]; norm_num
    _ ≤ ENNReal.ofReal (2 * (5 / s)) + ENNReal.ofReal K := by gcongr
    _ = ENNReal.ofReal (2 * (5 / s) + K) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (22 * (1 + M) ^ (-δ / 2)) := ENNReal.ofReal_le_ofReal hfin
end ReciprocityTheory.ChartRestriction.DS.Xi
