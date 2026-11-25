-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.dm_rank_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:15:04.021238+00:00
-- url     : https://prove2.me/submissions/c0e70204-9943-44f7-b66f-46489573cb8a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMoments

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (A B : Matrix (Fin n) (Fin n) ℂ) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc Module.finrank ℂ (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank ℂ ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) := by
        apply Submodule.finrank_mono
        rintro _ ⟨v, rfl⟩
        exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _
end ReciprocityTheory.ChartRestriction.DS.S7
