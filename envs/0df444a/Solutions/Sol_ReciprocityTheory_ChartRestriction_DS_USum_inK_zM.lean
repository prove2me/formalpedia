-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.USum.inK_zM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:25:00.87403+00:00
-- url     : https://prove2.me/submissions/4a8eb0af-024b-48ab-bf9b-849e57fc77cd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_InKRealSmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_Jm_comm_zM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
open ReciprocityTheory.ChartRestriction.DS.USum
variable {n : ℕ} {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS.USum
theorem _root_.solution {a b : Fin n} (hab : ε a = ε b) (c : ℂ) : inK ε (zM a b c) := by
  have hH : (zM a b c)ᴴ = -zM a b c := by
    ext i j
    have e1 : (a = j ∧ b = i) ↔ (b = i ∧ a = j) := and_comm
    have e2 : (b = j ∧ a = i) ↔ (a = i ∧ b = j) := and_comm
    simp only [zM, Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.single_apply, e1, e2]
    split_ifs <;> simp
  refine ⟨?_, (Jm_comm_zM hab c).symm⟩
  unfold inG
  rw [hH, Jm_comm_zM hab c, neg_mul, neg_add_cancel]
end ReciprocityTheory.ChartRestriction.DS.USum
