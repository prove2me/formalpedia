-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_localMult_eq_one_of_isRadical_c91ebf588e5e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:35.05262+00:00
-- url     : https://prove2.me/submissions/d7d84d3c-6969-4452-a95a-8abc9b3abb9e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_map_eq_maximalIdeal_of_isRadical_fa5b08ef435e

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {A : Type*} [CommRing A] {J W : Ideal A} (hJ : J.IsRadical)
    (hW : W ∈ J.minimalPrimes) : localMult J W = 1 := by
  have hWp : W.IsPrime := hW.1.1
  unfold localMult
  rw [dif_pos hWp, map_eq_maximalIdeal_of_isRadical hJ hW]
  have : IsSimpleModule (Localization.AtPrime W)
      (Localization.AtPrime W ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime W)) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal _))
  rw [Module.length_eq_one]
  rfl
end GroundTheory.Heights₂.Heights
