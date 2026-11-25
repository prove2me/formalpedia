-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPartGauss_isProjPrime_genericIdeal_2708c8f68489
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:44:33.27313+00:00
-- url     : https://prove2.me/submissions/1a93a730-ee60-47b3-ad27-a240a5a12c82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_AevalGenericIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_FiniteSupportLogCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_genericIdeal_isPrime_21e151008f95
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_genericIdeal_isHomog_b53edbad69d1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_genericIdeal_isRelevant_75bf1a3553bb

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
    IsProjPrime (genericIdeal P) :=
  ⟨genericIdeal_isPrime hP, genericIdeal_isHomog hP, genericIdeal_isRelevant hP⟩
end GroundTheory.Heights₂.Heights.VerticalPartGauss
