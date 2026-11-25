-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPartGauss_genericIdeal_isRelevant_75bf1a3553bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:23:05.165709+00:00
-- url     : https://prove2.me/submissions/0f287478-795c-41ed-b78c-aff2b5d09b79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_AevalGenericIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_FiniteSupportLogCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_map_mem_genericIdeal_iff_0ed5e7f8fd1e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isRelevant_finIdeal_iff_f29f08675567


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
    IsRelevant (genericIdeal P) := by
  obtain ⟨j, hj⟩ := (ObjectsChow.isRelevant_finIdeal_iff P).mpr hP.2.1.2.2
  refine ⟨j, fun h => hj ((map_mem_genericIdeal_iff hP (X j)).mp ?_)⟩
  rwa [map_X]
end GroundTheory.Heights₂.Heights.VerticalPartGauss
