-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.locallyIntegrable_comp_eval_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:41:51.284051+00:00
-- url     : https://prove2.me/submissions/cb07386a-01d1-45f7-8bf7-77228d4ddf6f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogIntSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} (i : Fin D) {g : ℂ → ℝ}
    (hg : LocallyIntegrable g volume) :
    LocallyIntegrable (fun z : Fin D → ℂ => g (z i)) volume := by
  classical
  intro x
  have hmeas : MeasurableSet (Set.pi Set.univ (fun j => Metric.closedBall (x j) (1 : ℝ))) :=
    MeasurableSet.univ_pi (fun j => measurableSet_closedBall)
  refine ⟨Set.pi Set.univ (fun j => Metric.closedBall (x j) 1),
    set_pi_mem_nhds Set.finite_univ (fun j _ => Metric.closedBall_mem_nhds (x j) one_pos), ?_⟩
  rw [← integrable_indicator_iff hmeas]
  have hf : ∀ j : Fin D, Integrable (fun w : ℂ => if j = i then (Metric.closedBall (x j) 1).indicator g w
      else (Metric.closedBall (x j) 1).indicator (fun _ => (1 : ℝ)) w) volume := by
    intro j
    split_ifs
    · exact (integrable_indicator_iff measurableSet_closedBall).mpr
        (hg.integrableOn_isCompact (isCompact_closedBall _ _))
    · exact (integrable_indicator_iff measurableSet_closedBall).mpr
        ((locallyIntegrable_const (1 : ℝ)).integrableOn_isCompact (isCompact_closedBall _ _))
  have hI := Integrable.fintype_prod (μ := fun _ : Fin D => (volume : Measure ℂ)) hf
  rw [volume_pi]
  refine hI.congr (Filter.Eventually.of_forall fun z => ?_)
  beta_reduce
  by_cases hz : z ∈ Set.pi Set.univ (fun j => Metric.closedBall (x j) (1 : ℝ))
  · rw [Set.indicator_apply, if_pos hz]
    rw [Set.mem_univ_pi] at hz
    rw [Finset.prod_eq_single i]
    · simp [Set.indicator_apply, hz i]
    · intro j _ hj
      simp [hj, Set.indicator_apply, hz j]
    · simp
  · rw [Set.indicator_apply, if_neg hz]
    rw [Set.mem_univ_pi] at hz
    push_neg at hz
    obtain ⟨j, hj⟩ := hz
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by split_ifs <;> simp [Set.indicator_apply, hj])
end ReciprocityTheory.AnForm.A
