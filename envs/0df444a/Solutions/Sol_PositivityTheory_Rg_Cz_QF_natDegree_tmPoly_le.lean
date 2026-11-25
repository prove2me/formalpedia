-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QF.natDegree_tmPoly_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:09.978451+00:00
-- url     : https://prove2.me/submissions/3d2cf763-d884-43c7-b9d3-ed6924caacc1

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PQdetFacts

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
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) :
    (tmPoly E k a b).natDegree ≤ if a = b then 1 else 0 := by
  rw [tmPoly]
  split_ifs with h
  · exact (natDegree_add_le _ _).trans (max_le (natDegree_X_sub_C_le _) (by rw [natDegree_C]; exact zero_le_one))
  · rw [zero_add, natDegree_C]
end PositivityTheory.Rg.Cz.QF
