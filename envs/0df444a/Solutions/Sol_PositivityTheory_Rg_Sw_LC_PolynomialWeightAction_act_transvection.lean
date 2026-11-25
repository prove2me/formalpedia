-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.act_transvection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:51.358095+00:00
-- url     : https://prove2.me/submissions/873a5521-6870-41f5-9b12-8483ffa7c6ac

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_TransvectionInv
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_Dsrc_inl
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_Dsrc_inr
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_fix_of_exp
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_transvection_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
theorem _root_.solution (t : Matrix.TransvectionStruct (Fin n) ℂ) (p : MvPolynomial (FinalTheorems m n) ℂ)
    (hp : Dsrc (m := m) t.j t.i p = 0) : act t.toMatrix p = p := by
  obtain ⟨i0, j0, hij, c⟩ := t
  simp only [Matrix.TransvectionStruct.toMatrix_mk] at hp ⊢
  refine fix_of_exp (Dsrc j0 i0) (act (Matrix.transvection i0 j0 c)) c ?_ ?_ p hp
  · rintro (⟨l, a⟩ | ⟨l, b⟩)
    · rw [Dsrc_inl]
      have hT : ∀ k, Matrix.transvection i0 j0 c l k = (if l = k then 1 else 0) + (if i0 = l ∧ j0 = k then c else 0) := by
        intro k; simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]
      simp only [act, aeval_X, Sum.elim_inl, hT]
      by_cases hl : l = i0
      · subst hl
        rw [Fintype.sum_eq_add l j0 hij (fun x hx => by simp [Ne.symm hx.1, Ne.symm hx.2])]
        simp [hij, Ne.symm hij]
      · rw [Fintype.sum_eq_single l (fun x hx => by simp [Ne.symm hx, Ne.symm hl])]
        simp [hl, Ne.symm hl]
    · rw [Dsrc_inr]
      simp only [act, aeval_X, Sum.elim_inr]
      rw [transvection_inv i0 j0 hij]
      have hT : ∀ k, Matrix.transvection i0 j0 (-c) k l = (if k = l then 1 else 0) + (if i0 = k ∧ j0 = l then -c else 0) := by
        intro k; simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]
      simp only [hT]
      by_cases hl : l = j0
      · subst hl
        rw [Fintype.sum_eq_add l i0 (Ne.symm hij) (fun x hx => by simp [hx.1, Ne.symm hx.2])]
        simp [hij, Ne.symm hij]
      · rw [Fintype.sum_eq_single l (fun x hx => by simp [hx, Ne.symm hl])]
        simp [hl, Ne.symm hl]
  · rintro (⟨l, a⟩ | ⟨l, b⟩)
    · by_cases hl : l = i0
      · exact ⟨Sum.inl (j0, a), 1, by simp [Dsrc_inl, hl], by simp [Dsrc_inl, Ne.symm hij]⟩
      · exact ⟨Sum.inl (j0, a), 0, by simp [Dsrc_inl, hl], by simp [Dsrc_inl, Ne.symm hij]⟩
    · by_cases hl : l = j0
      · exact ⟨Sum.inr (i0, b), -1, by simp [Dsrc_inr, hl], by simp [Dsrc_inr, hij]⟩
      · exact ⟨Sum.inr (i0, b), 0, by simp [Dsrc_inr, hl], by simp [Dsrc_inr, hij]⟩
end PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
