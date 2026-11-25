-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PoincareLelong_hypotheses_inhabited_053257e28e97
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:03:40.32405+00:00
-- url     : https://prove2.me/submissions/99d3d3ca-57b4-4d4c-a992-70544f1f61bd

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_space_dim_45905c840704
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_smooth_bump_81879bbf68ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_smoothNear_of_contDiff_8ca53b5543f3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_euclPot_53e03a97724f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_single_not_mem_bot_952292a2748a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace PoincareLelong
theorem _root_.solution :
    ∃ f : (Fin 2 → ℂ) → ℝ, (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)).IsPrime ∧
      ringKrullDim (MvPolynomial (Fin 2) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ))) = (1 + 1 : ℕ) ∧
      linForm (Pi.single 0 (1 : ℂ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ i : Fin 1, SmoothNear (zeroSet (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)))
        ((fun _ => euclPot) i)) ∧ f 0 = 1 := by
  obtain ⟨f, hs, hc, h0⟩ := exists_smooth_bump 2
  exact ⟨f, Ideal.isPrime_bot, space_dim 2, linForm_single_not_mem_bot 0, hs, hc,
    fun _ => smoothNear_of_contDiff (contDiff_euclPot 2), h0⟩
end PoincareLelong
end GroundTheory.Heights₂.Heights
