-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMult_betaB_X_292343fa3182
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:40:40.043661+00:00
-- url     : https://prove2.me/submissions/51069d21-09ff-4f69-94bd-89718d832911

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMult

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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMult
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {O : Type*} [CommRing O] [IsDomain O]
variable {Fε : Type*} [FunLike Fε (MvPolynomial (Coord n) ℤ) O]
  [RingHomClass Fε (MvPolynomial (Coord n) ℤ) O] (ε : Fε)
  (γ : MvPolynomial (Coord n) ℤ →+* MvPolynomial ι O)
  (hγ : ∀ {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}, IsWeightedHomogeneous (coordDeg n) F d →
    γ F = C (ε F) * ∏ k, X k ^ d k)
  (V : Ideal (MvPolynomial (Coord n) ℤ)) [(V.map ε).IsPrime]
include hγ
omit [IsDomain O] [RingHomClass Fε (MvPolynomial (Coord n) ℤ) O]
namespace GroundTheory.Heights₂.Heights.OrbitChartMult
theorem _root_.solution (p : Coord n) :
    betaB γ (V.map ε) (X p) = algebraMap (MvPolynomial ι O) (locB ι (V.map ε))
      (C (ε (X p)) * X p.1) := by
  rw [betaB, RingHom.comp_apply, hγ (isWeightedHomogeneous_X ℤ (coordDeg n) p)]
  congr 2
  simp [coordDeg, Pi.single_apply, pow_ite]
end GroundTheory.Heights₂.Heights.OrbitChartMult
