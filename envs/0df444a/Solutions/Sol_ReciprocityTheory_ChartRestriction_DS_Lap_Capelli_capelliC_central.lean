-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capelliC_central
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:58:03.966681+00:00
-- url     : https://prove2.me/submissions/d02019ae-43d0-4550-9b44-2a47c22d7426

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ColAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ProdOfFnUpdateEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_cols_not_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_rows_not_inj


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution (hE : GlRelR E) (x : ℂ) (a b : Fin n) : Commute (E a b) (capelliC E x) := by
  have h := cminor_comm E hE a b (id : Fin n → Fin n) id x
  simp only [id, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  by_cases hab : a = b
  · subst hab
    rw [show Function.update (id : Fin n → Fin n) a a = id from Function.update_eq_self a id, sub_self] at h
    exact sub_eq_zero.1 h
  · have h1 : cminor E (Function.update (id : Fin n → Fin n) b a) id x = 0 := by
      apply cminor_rows_not_inj
      intro hinj
      have : Function.update (id : Fin n → Fin n) b a b = Function.update (id : Fin n → Fin n) b a a := by
        simp [Function.update_of_ne hab]
      exact hab (hinj this).symm
    have h2 : cminor E id (Function.update (id : Fin n → Fin n) a b) x = 0 := by
      apply cminor_cols_not_inj E hE
      intro hinj
      have : Function.update (id : Fin n → Fin n) a b a = Function.update (id : Fin n → Fin n) a b b := by
        simp [Function.update_of_ne (Ne.symm hab)]
      exact hab (hinj this)
    rw [h1, h2, sub_self] at h
    exact sub_eq_zero.1 h
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
