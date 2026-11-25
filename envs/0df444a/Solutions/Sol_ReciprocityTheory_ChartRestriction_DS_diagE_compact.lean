-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.diagE_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:54:46.491847+00:00
-- url     : https://prove2.me/submissions/d3a76c70-be06-43f8-b671-e9d0956412a0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_E_comm_sgE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sgE_comm


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
variable {n : ℕ}
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b : Fin n) (h : ε a = ε b) :
    diagE ε E cp cm a b * diagE ε E cp cm b a - diagE ε E cp cm b a * diagE ε E cp cm a b =
      diagE ε E cp cm a a - diagE ε E cp cm b b := by
  have e1 := hE a b b a
  have e2 := sgE_comm hC ε a b b a h h.symm
  simp only [if_true] at e1 e2
  rw [sub_eq_iff_eq_add] at e1 e2
  unfold diagE
  rw [add_mul, mul_add, mul_add, add_mul, mul_add, mul_add, E_comm_sgE hEC ε a b b a,
    E_comm_sgE hEC ε b a a b, e1, e2]
  abel
end ReciprocityTheory.ChartRestriction.DS
