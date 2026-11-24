-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.exp_mem_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:57:21.577605+00:00
-- url     : https://prove2.me/submissions/39f7e8e0-1251-4057-a45a-d931009afc10

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
private theorem pow_mem_lemma {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (W : Submodule ℂ V) (A : V →L[ℂ] V) (hA : ∀ v ∈ W, A v ∈ W) (k : ℕ) :
    ∀ v ∈ W, (A ^ k) v ∈ W := by
  induction k with
  | zero => intro v hv; simpa using hv
  | succ k ih =>
    intro v hv
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    exact hA _ (ih v hv)
end ReciprocityTheory.ChartRestriction.DS.HW
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    [FiniteDimensional ℂ V] (W : Submodule ℂ V) (A : V →L[ℂ] V) (hA : ∀ v ∈ W, A v ∈ W) :
    ∀ v ∈ W, NormedSpace.exp A v ∈ W := by
  intro v hv
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL
    (ContinuousLinearMap.apply ℂ V v)
  refine (Submodule.closed_of_finiteDimensional W).mem_of_tendsto hs.tendsto_sum_nat
    (Filter.Eventually.of_forall fun m => ?_)
  refine Submodule.sum_mem _ fun k _ => ?_
  simp only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply]
  exact W.smul_mem _ (pow_mem_lemma W A hA k v hv)
end ReciprocityTheory.ChartRestriction.DS.HW
