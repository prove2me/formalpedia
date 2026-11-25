-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_factorAd_apply__c08584207034
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:59:06.616116+00:00
-- url     : https://prove2.me/submissions/252d6c04-511d-4c79-bc0a-631dd5ac6350

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_coord_apply__ef209eafcd1f
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_ofCoords_apply__59ec57a7c351

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
theorem _root_.solution (k : ℕ) (i : Fin k) (a b : Fin n) (F : Big n k M)
    (κ : Fin k → Fin n × Fin n) :
    factorAd (M := M) k i a b F κ =
      (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) -
        (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) := by
  first
  | (simp only [factorAd, ofCoords_apply', LinearMap.sub_apply]
     split_ifs <;> simp [coord_apply'])
  | (show ((if (κ i).1 = a then coord k (Function.update κ i (b, (κ i).2)) else 0) -
        (if (κ i).2 = b then coord k (Function.update κ i ((κ i).1, a)) else 0) :
        Big n k M →ₗ[ℂ] M) F = _
     split_ifs <;> simp [coord_apply'])
end ReciprocityTheory.ChartRestriction.DS
