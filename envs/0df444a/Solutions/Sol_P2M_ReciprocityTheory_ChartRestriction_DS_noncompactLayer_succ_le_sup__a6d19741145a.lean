-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_noncompactLayer_succ_le_sup__a6d19741145a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:20.370954+00:00
-- url     : https://prove2.me/submissions/3c27f862-9754-4e99-9999-095090b9732e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_map_noncompactLayer_le_sup

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
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (k : ℕ) :
    layer ε E V (k + 1) ≤ layer ε E V k ⊔ (ncV ε V (k + 1)).map (phi E (k + 1)) := by
  show layer ε E V k ⊔ ⨆ (a : Fin n) (b : Fin n) (_ : ε a ≠ ε b), (layer ε E V k).map (E a b) ≤ _
  exact sup_le le_sup_left (iSup_le fun a => iSup_le fun b => iSup_le fun hab => map_noncompactLayer_le_sup k a b hab)
end ReciprocityTheory.ChartRestriction.DS
