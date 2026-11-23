-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.eT_isGlRep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:29.942664+00:00
-- url     : https://prove2.me/submissions/7a1c0fe1-def9-449a-a5ed-85c362aa1932

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DSymmHypsInhabited

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
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ N} (hE : IsGlRep E) : IsGlRep (eT (n := n) E) := by
  intro a b c d
  have h := congrArg (Module.End.rTensorAlgHom ℂ N (Fock n)) (hE a b c d)
  rw [map_sub, map_sub, map_mul, map_mul] at h
  refine h.trans ?_
  congr 1 <;> split_ifs <;> first | rfl | simp
end ReciprocityTheory.ChartRestriction.DS
