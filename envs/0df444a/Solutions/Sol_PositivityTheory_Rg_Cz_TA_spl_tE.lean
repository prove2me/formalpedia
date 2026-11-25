-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TA.spl_tE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:49:23.274921+00:00
-- url     : https://prove2.me/submissions/17c22931-1b66-4a67-a73a-125546af945a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllB
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_merge_upd_left
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_merge_upd_right
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_spl_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  (q : P → Prop) [DecidablePred q]
omit [Fintype P]
namespace PositivityTheory.Rg.Cz.TA
theorem _root_.solution (S : Finset P) (F : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : TV n M P) :
    spl q (tE S F a b f) =
      tE (S.subtype q) (fun a b => tE (S.subtype fun p => ¬ q p) F a b) a b (spl q f) := by
  funext J I
  simp only [spl_apply, tE, lift, eAt, LinearMap.add_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Pi.add_apply]
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not S q, add_comm]
  congr 1
  · rw [← Finset.sum_subtype_eq_sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : I x = a
    · simp [h, merge_right, spl_apply, merge_upd_right]
    · simp [h, merge_right]
  · rw [← Finset.sum_subtype_eq_sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : J x = a
    · simp [h, merge_left, spl_apply, merge_upd_left]
    · simp [h, merge_left]
end PositivityTheory.Rg.Cz.TA
