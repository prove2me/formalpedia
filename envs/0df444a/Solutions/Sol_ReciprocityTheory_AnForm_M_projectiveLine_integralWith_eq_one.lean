-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.projectiveLine_integralWith_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:52:00.306174+00:00
-- url     : https://prove2.me/submissions/5266a4a4-17c4-4761-9239-95ba887c6cd7

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProjectiveLinePartitionContinuousCoe
import Theorems.Thm_ReciprocityTheory_AnForm_M_projectiveLine_sum_charts
import Theorems.Thm_ReciprocityTheory_AnForm_M_projectiveLine_second_chart_symm
import Theorems.Thm_ReciprocityTheory_AnForm_M_projectiveLine_locDens_first_chart
import Theorems.Thm_ReciprocityTheory_AnForm_M_projectiveLine_locDens_second_chart
import Theorems.Thm_ReciprocityTheory_AnForm_M_projectiveLine_partition_integrable
import Theorems.Thm_ReciprocityTheory_AnForm_integral_fsDens
import Theorems.Thm_ReciprocityTheory_AnForm_integral_fsDens_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology Set
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (P : ChartPartition p1) :
    integralWith p1 P (fun _ => fsPot) (fun _ => 1) = 1 := by
  unfold integralWith
  rw [projectiveLine_sum_charts]
  have e0 : ∫ y in (p1.chart p1i0).target,
      P.χ p1i0 ((p1.chart p1i0).symm y) * (fun _ => (1 : ℝ)) ((p1.chart p1i0).symm y) *
        locDens p1 (fun _ => fsPot) p1i0 y = ∫ u : ℂ, P.χ p1i0 (u : OnePoint ℂ) * fsDens u := by
    rw [show (p1.chart p1i0).target = univ from rfl, Measure.restrict_univ]
    simp_rw [projectiveLine_locDens_first_chart, mul_one]
    exact (volume_preserving_funUnique (Fin 1) ℂ).integral_comp'
      (fun u => P.χ p1i0 (u : OnePoint ℂ) * fsDens u)
  have e1 : ∫ y in (p1.chart p1i1).target,
      P.χ p1i1 ((p1.chart p1i1).symm y) * (fun _ => (1 : ℝ)) ((p1.chart p1i1).symm y) *
        locDens p1 (fun _ => fsPot) p1i1 y = ∫ u : ℂ, P.χ p1i1 (u : OnePoint ℂ) * fsDens u := by
    rw [show (p1.chart p1i1).target = univ from rfl, Measure.restrict_univ]
    simp_rw [projectiveLine_locDens_second_chart, mul_one]
    rw [← integral_fsDens_inv (fun v => P.χ p1i1 (v : OnePoint ℂ))]
    refine Eq.trans ((volume_preserving_funUnique (Fin 1) ℂ).integral_comp'
      (fun u => P.χ p1i1 ((p1.chart p1i1).symm (fun _ => u)) * fsDens u)) ?_
    refine integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))] with u hu
    have hu0 : u ≠ 0 := hu
    show P.χ p1i1 ((p1.chart p1i1).symm (fun _ => u)) * fsDens u = P.χ p1i1 (u⁻¹ : ℂ) * fsDens u
    rw [projectiveLine_second_chart_symm, if_neg hu0]
  rw [e0, e1, ← integral_add (projectiveLine_partition_integrable P p1i0) (projectiveLine_partition_integrable P p1i1)]
  simp_rw [← add_mul]
  have hs : ∀ u : ℂ, P.χ p1i0 (u : OnePoint ℂ) + P.χ p1i1 (u : OnePoint ℂ) = 1 := fun u => by
    rw [← projectiveLine_sum_charts (fun j => P.χ j (u : OnePoint ℂ)), P.sum_eq_one]
  simp_rw [hs, one_mul]
  exact integral_fsDens
end ReciprocityTheory.AnForm.M
