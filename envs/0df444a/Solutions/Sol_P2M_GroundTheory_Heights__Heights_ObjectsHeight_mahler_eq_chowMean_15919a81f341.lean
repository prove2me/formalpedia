-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_mahler_eq_chowMean_15919a81f341
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:55:43.546907+00:00
-- url     : https://prove2.me/submissions/4aa77080-5b2b-49c6-b9d9-58b383affd7c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_sphereMean_eq_integral_c09b214a98e7

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
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}
variable {k : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsHeight
theorem _root_.solution (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (h : HermNorm n)
    (hh : ∀ u, h.norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) (f : MvPolynomial (Fin k × Fin n) ℂ) :
    mahler h k f = IndefiniteRowSideFullHecke.ArithBezout.chowMean S k f :=
  sphereMean_eq_integral S hS h hh _
    (Real.measurable_log.comp (continuous_norm.comp (MvPolynomial.continuous_eval f)).measurable)
end GroundTheory.Heights₂.Heights.ObjectsHeight
