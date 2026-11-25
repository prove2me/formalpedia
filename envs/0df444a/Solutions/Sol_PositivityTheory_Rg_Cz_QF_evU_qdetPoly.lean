-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QF.evU_qdetPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:45:08.937627+00:00
-- url     : https://prove2.me/submissions/670e70a5-a7b6-4b80-9882-8019adb21676

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PQdetFacts
import Theorems.Thm_PositivityTheory_Rg_Cz_QF_evU_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_QF_evU_tmPoly

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
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) : evU u (qdetPoly E) = qdet E u := by
  simp only [qdetPoly, qdet, qminor, id, map_sum, map_mul, map_list_prod, List.map_ofFn, Function.comp_def,
    evU_tmPoly]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [evU_apply, eval₂_C]
  rfl
end PositivityTheory.Rg.Cz.QF
