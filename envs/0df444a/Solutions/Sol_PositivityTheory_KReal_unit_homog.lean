-- Prove2me | solution 1 for PositivityTheory.KReal.unit_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:41:28.565598+00:00
-- url     : https://prove2.me/submissions/d68bdf28-8a5e-4a9f-ab4e-1fc022224786

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreProj
import Theorems.Thm_PI_FHS_omE_apply_of_ne
import Theorems.Thm_PI_FockOneDegW_fockAct1_Eab_apply
import Theorems.Thm_PI_FockOneDegW_isKC_Eab
import Theorems.Thm_gradedOscillatorProperty


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
namespace PositivityTheory.KReal
theorem _root_.solution {p q r : ℕ} (a b : Ix p q) (i : ℕ) (P : Pol p q r 0) (hP : P ∈ homog (Ix p q × Ix r 0) i) :
    ∃ e, fockAct1 p q r 0 (Eab a b) P ∈ homog (Ix p q × Ix r 0) e := by
  by_cases hab : sameBlock a b
  · exact ⟨i, (gradedOscillatorProperty p q r 0).1 _ (PI.FockOneDegW.isKC_Eab hab) i P hP⟩
  have hP' : P.IsHomogeneous i := hP
  rw [PI.FockOneDegW.fockAct1_Eab_apply]
  rcases a with a | a <;> rcases b with b | b
  · exact absurd trivial hab
  · refine ⟨1 + (1 + i), Submodule.sum_mem _ fun c _ => ?_⟩
    rcases c with c | c
    · rw [PI.FHS.omE_apply_of_ne (by simp)]
      simp only [raiB, lowB, linePos, if_true, Bool.false_eq_true, if_false, LinearMap.mulLeft_apply]
      exact (isHomogeneous_X ℂ _).mul ((isHomogeneous_X ℂ _).mul hP')
    · exact c.elim0
  · refine ⟨i - 1 - 1, Submodule.sum_mem _ fun c _ => ?_⟩
    rcases c with c | c
    · rw [PI.FHS.omE_apply_of_ne (by simp)]
      simp only [raiB, lowB, linePos, if_true, Bool.false_eq_true, if_false, LinearMap.neg_apply]
      exact Submodule.neg_mem _ (hP'.pderiv.pderiv)
    · exact c.elim0
  · exact absurd trivial hab
end PositivityTheory.KReal
