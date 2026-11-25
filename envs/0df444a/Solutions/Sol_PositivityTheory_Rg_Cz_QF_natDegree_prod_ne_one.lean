-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QF.natDegree_prod_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:59:33.406711+00:00
-- url     : https://prove2.me/submissions/f4b6e03a-c6a0-4860-9a47-4dd15c280967

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
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) {σ : Equiv.Perm (Fin n)} (hσ : σ ≠ 1) :
    (List.ofFn fun k : Fin n => tmPoly E k (σ k) k).prod.natDegree + 2 ≤ n := by
  have h1 := natDegree_prod_le E σ
  have h2 := fixed_add_support σ
  have h3 := Equiv.Perm.two_le_card_support_of_ne_one hσ
  omega
end PositivityTheory.Rg.Cz.QF
