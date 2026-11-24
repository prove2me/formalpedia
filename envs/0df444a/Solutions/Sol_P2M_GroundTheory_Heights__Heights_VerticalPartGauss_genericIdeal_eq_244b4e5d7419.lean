-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPartGauss_genericIdeal_eq_244b4e5d7419
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:48.900666+00:00
-- url     : https://prove2.me/submissions/873f4c11-5341-472a-b7d0-f6f3b7a1d0d5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_AevalGenericIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_FiniteSupportLogCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_algebraMap_eq_3bee6135e2df

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
theorem _root_.solution (P : Ideal (MRing (PBlk n))) :
    genericIdeal P = (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).map
      (algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ)) := by
  rw [algebraMap_eq]
  rfl
end GroundTheory.Heights₂.Heights.VerticalPartGauss
