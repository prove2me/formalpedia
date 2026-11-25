-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.ktint_exp_apply_of_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:44.882355+00:00
-- url     : https://prove2.me/submissions/6af31eb3-a9f4-45a5-9c62-2b9d14bc4668

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KtintExpApplyOfEig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (c : ℂ) (v : E) (h : A v = c • v) :
    NormedSpace.exp A v = NormedSpace.exp c • v := by
  have hpow : ∀ k : ℕ, (A ^ k) v = c ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      show (A ^ k) (A v) = _
      rw [h, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hA := NormedSpace.expSeries_summable' (𝕂 := ℂ) A
  have hc := NormedSpace.expSeries_summable' (𝕂 := ℂ) c
  have e1 : NormedSpace.exp A = ∑' k : ℕ, ((k.factorial : ℂ)⁻¹) • A ^ k :=
    congr_fun (NormedSpace.exp_eq_tsum ℂ) A
  have e2 : NormedSpace.exp c = ∑' k : ℕ, ((k.factorial : ℂ)⁻¹) • c ^ k :=
    congr_fun (NormedSpace.exp_eq_tsum ℂ) c
  rw [e1, e2]
  have e3 := ContinuousLinearMap.map_tsum (ContinuousLinearMap.apply ℂ E v) hA
  simp only [ContinuousLinearMap.apply_apply] at e3
  rw [e3]
  simp only [_root_.smul_apply, hpow, smul_smul]
  exact Summable.tsum_smul_const hc v
end ReciprocityTheory.ChartRestriction.DS.HW
