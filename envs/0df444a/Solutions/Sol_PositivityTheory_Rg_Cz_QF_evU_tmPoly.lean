-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QF.evU_tmPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:07.749674+00:00
-- url     : https://prove2.me/submissions/7b61e156-06d2-4d7d-af23-868b3349f712

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PQdetFacts
import Theorems.Thm_PositivityTheory_Rg_Cz_QF_evU_apply

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
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) (k : ℕ) (a b : Fin n) :
    evU u (tmPoly E k a b) = Tm E (u - (k : ℂ)) a b := by
  rw [evU_apply, tmPoly, Tm]
  split_ifs <;> simp [eval₂_add, eval₂_sub, map_sub]
end PositivityTheory.Rg.Cz.QF
