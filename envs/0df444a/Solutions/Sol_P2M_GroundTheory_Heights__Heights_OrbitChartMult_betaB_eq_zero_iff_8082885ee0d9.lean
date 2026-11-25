-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMult_betaB_eq_zero_iff_8082885ee0d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:49:48.869031+00:00
-- url     : https://prove2.me/submissions/7411b7ee-e03f-4573-b4f7-db46e4247838

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMult
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_locB_injective_c62a6c2c8081

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
omit [Fintype ι] [DecidableEq ι] [RingHomClass Fε (MvPolynomial (Coord n) ℤ) O]
namespace GroundTheory.Heights₂.Heights.OrbitChartMult
theorem _root_.solution (F : MvPolynomial (Coord n) ℤ) :
    betaB γ (V.map ε) F = 0 ↔ γ F = 0 := by
  rw [betaB, RingHom.comp_apply, map_eq_zero_iff _ (locB_injective ι _)]
end GroundTheory.Heights₂.Heights.OrbitChartMult
