-- Prove2me | solution 1 for PI.ScRefExists.WF.fam_li
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:58.859853+00:00
-- url     : https://prove2.me/submissions/5ce6b065-b96c-4874-97d1-33418dc1bff5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_MemLAOfNsmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WFrameOf
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_ScRefExists_WF_hG_add_right
import Theorems.Thm_PI_ScRefExists_WF_hG_smul_right
import Theorems.Thm_PI_ScRefExists_WF_hG_sum_right
import Theorems.Thm_PI_ScRefExists_WF_hG_symm
import Theorems.Thm_PI_ScRefExists_WF_hG_zero_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open PI PI.ScRefExists PI.ScRefExists.WF
variable {I : Formalism.MainNotions.S.AutInst} {p : ℕ}
variable {r k : ℕ} {e f : Fin r → Fin I.n → I.E} {w : Fin (k + 1) → Fin I.n → I.E}
namespace PI.ScRefExists.WF
theorem _root_.solution (he : ∀ a b, hG I (e a) (e b) = 0) (hf : ∀ a b, hG I (f a) (f b) = 0)
    (hef : ∀ a b, hG I (e a) (f b) = if a = b then 1 else 0)
    (hw : ∀ i a, hG I (e a) (w i) = 0 ∧ hG I (f a) (w i) = 0) (hli : LinearIndependent I.E w) :
    LinearIndependent I.E (fam e f w) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [fam, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at hg
  have hfe : ∀ a b, hG I (f a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [hG_symm I (e b) (f a), hef b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  have hb : ∀ a, g (Sum.inr (Sum.inl a)) = 0 := by
    intro a
    have hw1 : ∀ i, hG I (e a) (w i) = 0 := fun i => (hw i a).1
    have h1 := congrArg (hG I (e a)) hg
    simpa [hG_add_right, hG_sum_right, hG_smul_right, he, hef, hw1, hG_zero_right] using h1
  have ha : ∀ a, g (Sum.inl a) = 0 := by
    intro a
    have hw2 : ∀ i, hG I (f a) (w i) = 0 := fun i => (hw i a).2
    have h1 := congrArg (hG I (f a)) hg
    simpa [hG_add_right, hG_sum_right, hG_smul_right, hf, hfe, hw2, hG_zero_right] using h1
  simp only [ha, hb, zero_smul, Finset.sum_const_zero, zero_add] at hg
  have hc := Fintype.linearIndependent_iff.1 hli (fun i => g (Sum.inr (Sum.inr i))) hg
  intro i
  rcases i with a | a | i
  · exact ha a
  · exact hb a
  · exact hc i
end PI.ScRefExists.WF
