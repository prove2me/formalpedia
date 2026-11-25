-- Prove2me | solution 1 for PositivityTheory.KReal.mem_polChi_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:38:31.106169+00:00
-- url     : https://prove2.me/submissions/19651a77-15f1-4835-9990-5ff6029a7ca8

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Theorems.Thm_PI_FockOneDegW_Core_key
import Theorems.Thm_PI_FockOneDegW_isKC_Eab
import Theorems.Thm_PositivityTheory_KReal_act_eq_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {p q r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution (c : ℂ) (x : Pol p q r s) : x ∈ polChi p q r s c ↔
    ∀ a b, sameBlock a b → fockAct1 p q r s (Eab a b) x = (if a = b then c else 0) • x := by
  unfold polChi jointEig
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]
  constructor
  · intro h a b hab
    have h1 := h ⟨Eab a b, PI.FockOneDegW.isKC_Eab hab⟩
    refine h1.trans ?_
    congr 1
    by_cases e : a = b
    · subst e
      simp [chiTr, Eab]
    · simp [chiTr, Eab, e, Matrix.trace_single_eq_of_ne _ _ _ e]
  · rintro h ⟨Z, hZ⟩
    change fockAct1 p q r s Z x = chiTr c Z • x
    rw [act_eq_sum (fockAct1 p q r s) Z]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    have key : ∀ a b, Z a b • fockAct1 p q r s (Eab a b) x = (if a = b then c * Z a a else 0) • x := by
      intro a b
      by_cases hab : sameBlock a b
      · rw [h a b hab, smul_smul]
        by_cases e : a = b
        · subst e
          rw [if_pos rfl, if_pos rfl, mul_comm]
        · rw [if_neg e, if_neg e, mul_zero]
      · have e : a ≠ b := by
          rintro rfl
          exact hab (by cases a <;> trivial)
        rw [hZ a b hab, if_neg e, zero_smul, zero_smul]
    simp only [key, ← Finset.sum_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    congr 1
    simp only [chiTr, Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
end PositivityTheory.KReal
