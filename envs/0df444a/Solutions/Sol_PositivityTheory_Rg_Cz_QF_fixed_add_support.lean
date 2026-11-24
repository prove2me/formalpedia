-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QF.fixed_add_support
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:52.011221+00:00
-- url     : https://prove2.me/submissions/7453351a-1810-4667-ab8d-99690cf97ef3

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
theorem _root_.solution {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (∑ k : Fin n, if σ k = k then 1 else 0) + σ.support.card = n := by
  rw [Finset.sum_boole, Nat.cast_id]
  have hs : σ.support = Finset.univ.filter (fun k => ¬ σ k = k) := by
    ext k
    simp [Equiv.Perm.mem_support]
  rw [hs, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
end PositivityTheory.Rg.Cz.QF
