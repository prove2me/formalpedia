-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StokesOnVariety_hypotheses_inhabited_33c8d7325eaa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:56:37.929736+00:00
-- url     : https://prove2.me/submissions/a2f5b0c3-e026-4a8f-bc56-35a16f1b089a

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
namespace StokesOnVariety
theorem _root_.solution :
    ∃ f : (Fin 2 → ℂ) → ℝ, (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)).IsPrime ∧
      ringKrullDim (MvPolynomial (Fin 2) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ))) = (1 + 1 : ℕ) ∧
      SmoothNear (zeroSet (⊥ : Ideal (MvPolynomial (Fin 2) ℂ))) f ∧
      SmoothNear (zeroSet (⊥ : Ideal (MvPolynomial (Fin 2) ℂ))) euclPot ∧
      (∀ i : Fin 1, SmoothNear (zeroSet (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)))
        ((fun _ => euclPot) i)) ∧
      (HasCompactSupport f ∨ HasCompactSupport (euclPot : (Fin 2 → ℂ) → ℝ)) ∧ f 0 = 1 := by
  obtain ⟨f, hs, hc, h0⟩ := exists_smooth_bump 2
  exact ⟨f, Ideal.isPrime_bot, space_dim 2, smoothNear_of_contDiff hs,
    smoothNear_of_contDiff (contDiff_euclPot 2), fun _ => smoothNear_of_contDiff (contDiff_euclPot 2),
    Or.inl hc, h0⟩
end StokesOnVariety
end GroundTheory.Heights₂.Heights
