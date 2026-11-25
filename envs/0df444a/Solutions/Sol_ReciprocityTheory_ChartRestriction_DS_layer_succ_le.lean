-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.layer_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:56:33.989478+00:00
-- url     : https://prove2.me/submissions/2e6867d0-29f3-4fa2-b6c2-011be78f938e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_noncompactLayer_succ_le_sup__a6d19741145a

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
theorem _root_.solution (hE : IsGlRep E) (hV : IsKStableSub ε E V) (k : ℕ) :
    layer ε E V (k + 1) ≤ layer ε E V k ⊔ (ncV ε V (k + 1)).map (phi E (k + 1)) := noncompactLayer_succ_le_sup' k
end ReciprocityTheory.ChartRestriction.DS
