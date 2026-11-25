-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QF.natDegree_qdetPoly_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:59:36.897837+00:00
-- url     : https://prove2.me/submissions/d2cba9ce-ab8c-45ef-aeb1-2579826b6d93

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PQdetFacts
import Theorems.Thm_PositivityTheory_Rg_Cz_QF_natDegree_prod_le
import Theorems.Thm_PositivityTheory_Rg_Cz_QF_fixed_add_support

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
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) : (qdetPoly E).natDegree ≤ n := by
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le E σ).trans ?_)
  have := fixed_add_support σ
  omega
end PositivityTheory.Rg.Cz.QF
