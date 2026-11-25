-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.gelfand_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:38:25.168089+00:00
-- url     : https://prove2.me/submissions/5554ad5d-2c56-4382-a444-ff3ba25a8efc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_Lemmata_MiscLemmasP_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Gelfand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ePow_comm

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
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (k : ℕ) (a b : Fin n) :
    E a b * gelfand E k = gelfand E k * E a b := by
  have h : E a b * gelfand E k - gelfand E k * E a b = 0 := by
    unfold gelfand
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp_rw [ePow_comm hE]
    simp [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
  exact sub_eq_zero.mp h
end ReciprocityTheory.ChartRestriction.DS
