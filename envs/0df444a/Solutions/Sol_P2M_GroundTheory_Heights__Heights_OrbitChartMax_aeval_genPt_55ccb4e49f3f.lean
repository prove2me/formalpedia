-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_genPt_55ccb4e49f3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:29.698501+00:00
-- url     : https://prove2.me/submissions/8127c66c-9a07-4da3-a1b1-96074d2e5f79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMax

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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMax
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (V : Ideal (MvPolynomial (Coord n) ℤ)) [V.IsPrime]
omit [Fintype ι] [DecidableEq ι] [V.IsPrime]
namespace GroundTheory.Heights₂.Heights.OrbitChartMax
theorem _root_.solution (F : MvPolynomial (Coord n) ℤ) :
    aeval (genPt V) F = algebraMap _ (FractionRing (MvPolynomial (Coord n) ℤ ⧸ V))
      (Ideal.Quotient.mk V F) := by
  have h : (aeval (genPt V)).toRingHom =
      (algebraMap _ (FractionRing (MvPolynomial (Coord n) ℤ ⧸ V))).comp (Ideal.Quotient.mk V) :=
    MvPolynomial.ringHom_ext (fun a ↦ RingHom.congr_fun (RingHom.ext_int
      ((aeval (genPt V)).toRingHom.comp C)
      (((algebraMap _ (FractionRing (MvPolynomial (Coord n) ℤ ⧸ V))).comp
        (Ideal.Quotient.mk V)).comp C)) a)
      (fun p ↦ by simp [genPt])
  exact DFunLike.congr_fun h F
end GroundTheory.Heights₂.Heights.OrbitChartMax
