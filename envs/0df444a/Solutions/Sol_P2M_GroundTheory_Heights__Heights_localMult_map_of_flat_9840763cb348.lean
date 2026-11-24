-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_localMult_map_of_flat_9840763cb348
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:46.104848+00:00
-- url     : https://prove2.me/submissions/da704e53-c67a-4184-ba9a-44c4d21e5a40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFundCycleBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMinimalPrimeComap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRadicalBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFundCycleBaseChange

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
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (J W : Ideal A) [W.IsPrime] (W' : Ideal B) [W'.IsPrime] [W'.LiesOver W]
    (hfib : (W.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime W')) =
      IsLocalRing.maximalIdeal (Localization.AtPrime W')) :
    localMult (J.map (algebraMap A B)) W' = localMult J W := by
  let := Localization.AtPrime.algebraOfLiesOver W W'
  have : IsLocalHom (algebraMap (Localization.AtPrime W) (Localization.AtPrime W')) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have htow : (algebraMap (Localization.AtPrime W) (Localization.AtPrime W')).comp
      (algebraMap A (Localization.AtPrime W)) =
      (algebraMap B (Localization.AtPrime W')).comp (algebraMap A B) := by
    ext x
    exact Localization.localRingHom_to_map _ _ _ Ideal.LiesOver.over x
  have hmap : ∀ I : Ideal A, (I.map (algebraMap A (Localization.AtPrime W))).map
      (algebraMap (Localization.AtPrime W) (Localization.AtPrime W')) =
      (I.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime W')) := by
    intro I
    rw [Ideal.map_map, Ideal.map_map, htow]
  have key := IsLocalRing.length_baseChange (Localization.AtPrime W) (Localization.AtPrime W')
    (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W)))
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime W')
    (J.map (algebraMap A (Localization.AtPrime W)))).toLinearEquiv.length_eq, hmap,
    ← IsLocalization.AtPrime.map_eq_maximalIdeal W (Localization.AtPrime W), hmap, hfib] at key
  have : IsSimpleModule (Localization.AtPrime W')
      (Localization.AtPrime W' ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime W')) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal _))
  rw [Module.length_eq_one (R := Localization.AtPrime W')
    (M := Localization.AtPrime W' ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime W')), mul_one] at key
  unfold localMult
  rw [dif_pos ‹W'.IsPrime›, dif_pos ‹W.IsPrime›, key]
end GroundTheory.Heights₂.Heights
