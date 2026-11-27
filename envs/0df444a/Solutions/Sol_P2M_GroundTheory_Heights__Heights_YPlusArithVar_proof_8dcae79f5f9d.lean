-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_YPlusArithVar_proof_8dcae79f5f9d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:12:50.775797+00:00
-- url     : https://prove2.me/submissions/e3a04c0e-7808-448e-ba17-bf65bb8c7896

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusArithVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_isHorizontal_cfaf0a26d8e3


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
namespace GroundTheory.Heights₂.Heights
namespace YPlusArithVar
theorem _root_.solution (hPrime : ChartPrimality.Statement) (hDim : ExtensionDimension.Statement) :
    YPlusArithVar.Statement := by
  intro ι _ _ n P D Ω _ y x' E hR hA
  obtain ⟨Q, hQ⟩ := hPrime ι n P D
  obtain ⟨_, _, _, hd⟩ := hA
  rw [← hR.ext_eq]
  refine ⟨inferInstance, hQ ▸ Q.isMultiProjPrime, hQ ▸ Q.isHorizontal, ?_⟩
  rw [← hR.ideal_eq] at hd
  change ringKrullDim (MvPolynomial (Coord D.extSizes) ℤ ⧸ D.extIdeal) = _
  rw [hDim ι n P D]
  change ringKrullDim (MvPolynomial (Coord n) ℤ ⧸ P.ideal) + 1 = _
  change ringKrullDim (MvPolynomial (Coord n) ℤ ⧸ P.ideal) = _ at hd
  rw [hd, Fintype.card_option]
  norm_cast
end YPlusArithVar
end GroundTheory.Heights₂.Heights
