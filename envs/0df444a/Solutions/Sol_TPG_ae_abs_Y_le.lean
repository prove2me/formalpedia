-- Prove2me | solution 1 for TPG.ae_abs_Y_le
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:52:46.727363+00:00
-- url     : https://prove2.me/submissions/f5e5c270-3480-4605-8302-262e98a873cd

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Markov
import Theorems.Thm_TPG_trajLaw_eq_sum_map

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

/-- The embedding of a reward vector along a fixed state/action path is measurable. -/
private lemma TPG_measurable_embedPath {S : Type} [MeasurableSpace S] {T : ℕ}
    (x : Fin T → S) (z : Fin T → Bool) :
    Measurable (embedPath x z : (Fin T → ℝ) → Traj S T) := by
  unfold embedPath
  exact measurable_pi_lambda _ fun t =>
    measurable_const.prodMk (measurable_const.prodMk (measurable_pi_apply t))

/-- The reward coordinate of a trajectory is measurable. -/
private lemma TPG_measurable_Y {S : Type} [MeasurableSpace S] {T : ℕ} (t : Fin T) :
    Measurable (Y t : Traj S T → ℝ) := by
  unfold Y
  exact (measurable_pi_apply t).snd.snd

theorem solution {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (q : ℕ → ℝ) (M : ℝ) (hM : E.RewardBound M) :
    ∀ᵐ ω ∂(E.trajLaw T q), ∀ t : Fin T, |Y t ω| ≤ M := by
  rw [TPG.trajLaw_eq_sum_map, ae_finsetSum_measure_iff]
  intro p _
  refine Measure.ae_smul_measure ?_ _
  have hset : MeasurableSet {ω : Traj S T | ∀ t : Fin T, |Y t ω| ≤ M} := by
    have : {ω : Traj S T | ∀ t : Fin T, |Y t ω| ≤ M}
        = ⋂ t : Fin T, {ω : Traj S T | |Y t ω| ≤ M} := by
      ext ω; simp
    rw [this]
    exact MeasurableSet.iInter fun t =>
      measurableSet_le (TPG_measurable_Y t).abs measurable_const
  rw [ae_map_iff (TPG_measurable_embedPath p.1 p.2).aemeasurable hset]
  have hcoord : ∀ t : Fin T, ∀ᵐ y ∂(E.R (p.1 t) (p.2 t)), |y| ≤ M := by
    intro t
    have h1 : Set.Icc (-M) M ∈ ae (E.R (p.1 t) (p.2 t)) :=
      (mem_ae_iff_prob_eq_one measurableSet_Icc).2 (hM (p.1 t) (p.2 t))
    filter_upwards [h1] with y hy
    exact abs_le.2 hy
  unfold Env.rewardLaw
  refine (Filter.eventually_all.2 fun t =>
    Measure.tendsto_eval_ae_ae.eventually (hcoord t)).mono fun y hy t => ?_
  exact hy t
