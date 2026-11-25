-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.vanS_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:29:28.498032+00:00
-- url     : https://prove2.me/submissions/4c9d695b-c379-4cd5-b927-d795a9354fa6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
theorem _root_.solution (hn : 1 ≤ n) {a : ℕ} {G : V n → ℂ} {S : Fin n → V n → ℂ}
    (hG : G =O[𝓝 0] fun z => ‖z‖ ^ a) {c : ℝ} (hc : 0 < c)
    (hS : ∀ᶠ z in 𝓝 0, c * ‖z‖ ^ 2 ≤ ∑ k, ‖S k z‖ ^ 2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (‖G z‖ ^ 2 *
      (∑ k, ‖S k z‖ ^ 2) ^ (-((a : ℝ) + (n : ℝ) - 1 / 2))) < ⊤ := by
  obtain ⟨C, hCpos, hC⟩ := hG.exists_pos
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hC.bound.and hS)
  refine ⟨ρ, hρ, ?_⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set β : ℝ := (a : ℝ) + (n : ℝ) - 1 / 2 with hβ
  have hβpos : 0 < β := by
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith
  set K : ℝ := C ^ 2 * c ^ (-β) with hK
  have hKpos : 0 < K := by positivity
  have hfin : Module.finrank ℝ (V n) = 2 * n := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have hgi : MeasureTheory.IntegrableOn (fun z : V n => K * ‖z‖ ^ (-(2 * (n : ℝ) - 1)))
      (Metric.ball 0 ρ) := by
    refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (C := K) (α := 2 * (n : ℝ) - 1) ?_ ?_ ?_ ?_
    · rw [hfin]; omega
    · rw [hfin]; push_cast; linarith
    · refine MeasureTheory.ae_of_all _ fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · exact (measurable_const.mul (measurable_norm.pow_const _)).aestronglyMeasurable
  have hlt := (MeasureTheory.hasFiniteIntegral_iff_ofReal
    (MeasureTheory.ae_of_all _ fun z => by positivity)).mp hgi.2
  refine lt_of_le_of_lt (MeasureTheory.lintegral_mono_ae ?_) hlt
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball,
    MeasureTheory.ae_restrict_of_ae (MeasureTheory.compl_mem_ae_iff.mpr
      (MeasureTheory.measure_singleton (0 : V n)))] with z hz hz0
  have hz0' : z ≠ 0 := hz0
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0'
  obtain ⟨h1, h2⟩ := hball z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
  apply ENNReal.ofReal_le_ofReal
  have e1 : ‖G z‖ ^ 2 ≤ C ^ 2 * ‖z‖ ^ (2 * a) := by
    calc ‖G z‖ ^ 2 ≤ (C * ‖z‖ ^ a) ^ 2 := by gcongr
      _ = C ^ 2 * ‖z‖ ^ (2 * a) := by ring
  have e2 : (∑ k, ‖S k z‖ ^ 2) ^ (-β) ≤ (c * ‖z‖ ^ 2) ^ (-β) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
  have e3 : (c * ‖z‖ ^ 2) ^ (-β) = c ^ (-β) * ‖z‖ ^ (-2 * β) := by
    rw [Real.mul_rpow hc.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hzpos.le]
    ring_nf
  have e4 : ‖z‖ ^ (2 * a) * ‖z‖ ^ (-2 * β) = ‖z‖ ^ (-(2 * (n : ℝ) - 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hzpos]
    congr 1
    rw [hβ]
    push_cast
    ring
  calc ‖G z‖ ^ 2 * (∑ k, ‖S k z‖ ^ 2) ^ (-β) ≤ (C ^ 2 * ‖z‖ ^ (2 * a)) * (c * ‖z‖ ^ 2) ^ (-β) :=
        mul_le_mul e1 e2 (by positivity) (by positivity)
    _ = K * ‖z‖ ^ (-(2 * (n : ℝ) - 1)) := by rw [e3, hK, ← e4]; ring
end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
