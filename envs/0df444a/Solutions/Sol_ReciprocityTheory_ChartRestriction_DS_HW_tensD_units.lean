-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.tensD_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:23:20.59013+00:00
-- url     : https://prove2.me/submissions/1329950b-20a1-46da-b890-911d6daf92cd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_tensD_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_tensOp_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_tensTau_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.HW.tensOp_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.HW.tensTau_coe



set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {ι : Type} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) (a b : Fin n) :
    ((tensD T dρ (Matrix.single a b 1) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)) :
      Module.End ℂ (PiLp 2 (fun _ : ι => T.V))) =
      tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)) a b := by
  refine LinearMap.ext fun x => PiLp.ext fun i => ?_
  simp [tensAct, tensD_apply, kunits]
end ReciprocityTheory.ChartRestriction.DS.HW
