-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QF.natDegree_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:41:51.955152+00:00
-- url     : https://prove2.me/submissions/9b8c778a-1f82-42f6-9695-03a60e5aa98e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PQdetFacts
import Theorems.Thm_PositivityTheory_Rg_Cz_QF_natDegree_tmPoly_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.QF
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace PositivityTheory.Rg.Cz.QF
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) (σ : Equiv.Perm (Fin n)) :
    (List.ofFn fun k : Fin n => tmPoly E k (σ k) k).prod.natDegree ≤
      ∑ k : Fin n, if σ k = k then 1 else 0 := by
  refine (natDegree_list_prod_le _).trans ?_
  rw [List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_le_sum fun k _ => natDegree_tmPoly_le E k (σ k) k
end PositivityTheory.Rg.Cz.QF
