-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.actU_dY_actU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:24:19.324845+00:00
-- url     : https://prove2.me/submissions/aceabb93-6163-4153-9533-03a6044ba4c7

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_actU_X
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_actU_lf
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_actU_comp
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_actU_one
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_dY_X
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_dY_lf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KSplit
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.SiegelWeilFormula.KSplit
theorem _root_.solution (V : Matrix (Fin m) (Fin m) ℂ) (hV : V ∈ unitaryGroup (Fin m) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ)
    (P : PX m n) : actU V (dY Y (actU (star V) P)) = dY (star V * Y * V) P := by
  have hid : ∀ Q : PX m n, actU V (actU (star V) Q) = Q := fun Q => by
    rw [actU_comp, (mem_unitaryGroup_iff'.1 hV), actU_one]
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : actU (n := n) (star V) (C a) = C a := by simp [actU]
    rw [this, derivation_C, map_zero, derivation_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp =>
    have key : actU V (dY Y (actU (star V) (X k))) = dY (star V * Y * V) (X k) := by
      obtain ⟨a, i, b⟩ := k
      rw [actU_X, dY_lf, actU_lf, dY_X]
      congr 1
      cases b
      · simp [am, dm, Matrix.mul_assoc]
      · have h1 : (star V).map star = Vᵀ := by ext c e; simp [star_eq_conjTranspose]
        have h2 : V.map star = (star V)ᵀ := by ext c e; simp [star_eq_conjTranspose]
        simp only [am, dm, if_true, h1, h2, transpose_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hid, hid, hp, key,
      Derivation.leibniz, smul_eq_mul, smul_eq_mul]
end PositivityTheory.SiegelWeilFormula.KSplit
