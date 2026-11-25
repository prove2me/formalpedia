-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.gradT_cpT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:48.134527+00:00
-- url     : https://prove2.me/submissions/36aa652c-8cc2-4eab-bc1e-39ebe062bd32

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DSymmHypsInhabited
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_fock_inv_cp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (i a : Fin n) : gradT (N := N) * cpT i a = -(cpT i a * gradT) := by
  have h := congrArg (Module.End.lTensorAlgHom ℂ (Fock n) N) (fock_inv_cp (n := n) i a)
  simp only [map_neg, map_mul] at h
  exact h
end ReciprocityTheory.ChartRestriction.DS
