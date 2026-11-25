-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPartGauss_genericIdeal_isPrime_21e151008f95
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:23:02.668668+00:00
-- url     : https://prove2.me/submissions/a4922e05-1947-44e2-969d-1114715e93fe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_AevalGenericIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_FiniteSupportLogCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_genericIdeal_eq_244b4e5d7419
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_finIdeal_isPrime_530e89cd1eaf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_disjoint_constUnits_690a47693f08

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.VerticalPartGauss
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal coeffGaussNorm)
open ObjectsChow (genericIdeal)
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.VerticalPartGauss
theorem _root_.solution {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    (genericIdeal P).IsPrime := by
  rw [genericIdeal_eq]
  exact IsLocalization.isPrime_of_isPrime_disjoint (constUnits n) _ _ (finIdeal_isPrime hP)
    (disjoint_constUnits hP)
end GroundTheory.Heights₂.Heights.VerticalPartGauss
