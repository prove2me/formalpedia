-- Prove2me | solution 1 for PI.ZuckTensorWork.revNum_rhoN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:20:44.953335+00:00
-- url     : https://prove2.me/submissions/b955614b-daf2-466d-a1ad-16c4dd6c0530

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_RevNum
import Theorems.Thm_PI_ZuckTensorWork_Cj_mk_un
import Theorems.Thm_PI_ZuckTensorWork_Cj_un_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.ZuckTensorWork.Cj.mk_un
attribute [local simp] PI.ZuckTensorWork.Cj.un_mk



set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
variable {n : ℕ}
namespace PI.ZuckTensorWork
theorem _root_.solution (ε : Fin n → Bool) (a : Fin n) : rhoN (revE ε) a = - rhoN ε (Fin.rev a) := by
  have h1 : #(univ.filter fun b => a < b ∧ revE ε b ≠ revE ε a) =
      #(univ.filter fun b => b < Fin.rev a ∧ ε b ≠ ε (Fin.rev a)) := by
    apply Finset.card_nbij' Fin.rev Fin.rev
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨mem_univ _, Fin.rev_lt_rev.mpr hb.2.1, hb.2.2⟩
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨mem_univ _, Fin.lt_rev_iff.mpr hb.2.1, by simp only [revE, Fin.rev_rev]; exact hb.2.2⟩
    · intro b _; exact Fin.rev_rev b
    · intro b _; exact Fin.rev_rev b
  have h2 : #(univ.filter fun b => b < a ∧ revE ε b ≠ revE ε a) =
      #(univ.filter fun b => Fin.rev a < b ∧ ε b ≠ ε (Fin.rev a)) := by
    apply Finset.card_nbij' Fin.rev Fin.rev
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨mem_univ _, Fin.rev_lt_rev.mpr hb.2.1, hb.2.2⟩
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨mem_univ _, Fin.rev_lt_iff.mpr hb.2.1, by simp only [revE, Fin.rev_rev]; exact hb.2.2⟩
    · intro b _; exact Fin.rev_rev b
    · intro b _; exact Fin.rev_rev b
  simp only [rhoN]
  rw [h1, h2]
  ring
end PI.ZuckTensorWork
