-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.regularAtlas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:25:14.505429+00:00
-- url     : https://prove2.me/submissions/40e02e18-e991-4f64-8110-85cece2d3b0d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Theorems.Thm_ReciprocityTheory_AnForm_M_pa_compat_chart
import Theorems.Thm_ReciprocityTheory_AnForm_M_pa_compat_aff
import Theorems.Thm_ReciprocityTheory_AnForm_M_atlasOfCompat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : RegularAtlasStatement := by
  intro e X _ _ _ A
  have hloc : ∀ x : X, ∃ (j : Fin A.n) (r : ℝ), 0 < r ∧ x ∈ (A.chart j).source ∧
      Metric.ball (A.chart j x) r ⊆ (A.chart j).target := by
    intro x
    obtain ⟨j, hj⟩ := A.cover x
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp (A.chart j).open_target _ ((A.chart j).map_source hj)
    exact ⟨j, r, hr, hj, hb⟩
  choose J R hR hJ hball using hloc
  have ha : ∀ x, (((3 / R x : ℝ)) : ℂ) ≠ 0 := fun x =>
    Complex.ofReal_ne_zero.mpr (div_pos (by norm_num) (hR x)).ne'
  let ψ : X → OpenPartialHomeomorph X (Fin e → ℂ) := fun x =>
    (A.chart (J x)).transHomeomorph (pa_aff (((3 / R x : ℝ)) : ℂ) (ha x) (A.chart (J x) x))
  have hψc : ∀ x, IsCompatChart A (ψ x) := fun x =>
    pa_compat_aff A _ (pa_compat_chart A (J x)) _ (ha x) _
  let U : X → Set X := fun x => (ψ x).source ∩ (ψ x) ⁻¹' Metric.ball 0 1
  have hUo : ∀ x, IsOpen (U x) := fun x => (ψ x).isOpen_inter_preimage Metric.isOpen_ball
  have hUx : ∀ x, x ∈ U x := fun x => by
    refine ⟨hJ x, ?_⟩
    show (((3 / R x : ℝ)) : ℂ) • (A.chart (J x) x - A.chart (J x) x) ∈ Metric.ball (0 : Fin e → ℂ) 1
    simp
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo (fun x _ => Set.mem_iUnion.mpr ⟨x, hUx x⟩)
  let φ : Fin t.card → OpenPartialHomeomorph X (Fin e → ℂ) := fun i => ψ (t.equivFin.symm i)
  have hcov : ∀ x, ∃ i, x ∈ (φ i).source ∧ φ i x ∈ Metric.ball (0 : Fin e → ℂ) 1 := by
    intro x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    refine ⟨t.equivFin ⟨y, hy⟩, ?_⟩
    simp only [φ, Equiv.symm_apply_apply]
    exact hxy
  obtain ⟨B, hAB, hB1, hB2⟩ := atlasOfCompat A φ (fun i => hψc _) (fun x => (hcov x).imp fun i h => h.1)
  refine ⟨B, hAB, fun j => ?_, fun x => ?_⟩
  · obtain ⟨i, hi⟩ := hB2 j
    rw [hi]
    intro w hw
    have hw' : ‖w‖ ≤ 2 := by simpa using hw
    set y := t.equivFin.symm i
    change (((3 / R y : ℝ)) : ℂ)⁻¹ • w + A.chart (J y) y ∈ (A.chart (J y)).target
    apply hball
    have hRy := hR y
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hRy), inv_div]
    calc R y / 3 * ‖w‖ ≤ R y / 3 * 2 := by gcongr
      _ < R y := by linarith
  · obtain ⟨i, hi1, hi2⟩ := hcov x
    obtain ⟨j, hj⟩ := hB1 i
    exact ⟨j, hj ▸ hi1, hj ▸ hi2⟩
end ReciprocityTheory.AnForm.M
