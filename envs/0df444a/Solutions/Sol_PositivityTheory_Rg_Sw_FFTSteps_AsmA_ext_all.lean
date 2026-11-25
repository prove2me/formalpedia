-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmA.ext_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:09:56.735259+00:00
-- url     : https://prove2.me/submissions/d294d9af-f09e-40d2-a046-2852553a2394

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTB
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmA_act_act
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmA_continuous_act_eval
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmA_eval_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.AsmA
variable {ι A B : Type} [Fintype ι] [DecidableEq ι]
namespace PositivityTheory.Rg.Sw.FFTSteps.AsmA
theorem _root_.solution (hE : Ext) [Fintype A] [Fintype B] {p : PV ι A B} (hp : IsInv p) (M : Matrix ι ι ℂ)
    (z : (ι × A) ⊕ (ι × B) → ℂ) :
    eval (act M (M.map star) z) p = eval (act 1 (M.transpose * M.map star) z) p := by
  have key : ∀ M : Matrix ι ι ℂ, M.det ≠ 0 →
      eval (act M (M.map star) z) p = eval (act 1 (M.transpose * M.map star) z) p := by
    intro M hM
    have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
    have h1 : M⁻¹ * (M.transpose).transpose = 1 := by
      rw [Matrix.transpose_transpose]; exact Matrix.nonsing_inv_mul M hu
    have hq := hE ι A B p hp M⁻¹ M.transpose h1
    conv_lhs => rw [← hq]
    rw [eval_sub, act_act, Matrix.nonsing_inv_mul M hu]
  let F : ℂ → ℂ := fun t => eval (act (M + t • 1) ((M + t • 1).map star) z) p -
    eval (act 1 ((M + t • (1 : Matrix ι ι ℂ)).transpose * (M + t • 1).map star) z) p
  have c1 : Continuous fun t : ℂ => M + t • (1 : Matrix ι ι ℂ) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hF : Continuous F :=
    (continuous_act_eval c1 (c1.matrix_map continuous_star) z p).sub
      (continuous_act_eval continuous_const (c1.matrix_transpose.mul (c1.matrix_map continuous_star)) z p)
  let S := {t : ℂ | (Matrix.charpoly (-M)).IsRoot t}
  have hS : S.Countable := (Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic (-M)).ne_zero).countable
  have hd : Dense Sᶜ := hS.dense_compl ℂ
  have hz : Set.EqOn F (fun _ => 0) Sᶜ := by
    intro t ht
    have hdet : (M + t • (1 : Matrix ι ι ℂ)).det ≠ 0 := by
      intro h0
      apply ht
      show (Matrix.charpoly (-M)).eval t = 0
      rw [Matrix.eval_charpoly]
      have e : Matrix.scalar ι t - -M = M + t • (1 : Matrix ι ι ℂ) := by
        rw [sub_neg_eq_add, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, add_comm]
      rw [e]; exact h0
    simp only [F, key _ hdet, sub_self]
  have h0 := congrFun (hF.ext_on hd continuous_const hz) 0
  simp only [F, zero_smul, add_zero] at h0
  exact sub_eq_zero.mp h0
end PositivityTheory.Rg.Sw.FFTSteps.AsmA
