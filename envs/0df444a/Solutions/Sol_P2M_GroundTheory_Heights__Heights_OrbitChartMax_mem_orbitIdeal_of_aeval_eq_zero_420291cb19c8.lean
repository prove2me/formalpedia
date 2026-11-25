-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMax_mem_orbitIdeal_of_aeval_eq_zero_420291cb19c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:05:10.077715+00:00
-- url     : https://prove2.me/submissions/cb4adb86-de7f-4eb2-a7a2-3b1f211343cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMax
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_mul_of_homog_613ef6f28d4a

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
namespace GroundTheory.Heights₂.Heights.OrbitChartMax
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ))
    {G : MvPolynomial (Coord n) ℤ} {b : ι → ℕ} (hG : IsWeightedHomogeneous (coordDeg n) G b)
    (h0 : aeval (flatCone x) G = 0) : G ∈ orbitIdeal x := by
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap]
  have e : (fun p : Coord n ↦ C (flatCone x p) * (X p.1 : MvPolynomial ι (AlgebraicClosure ℚ))) =
      fun p ↦ (X p.1 : MvPolynomial ι (AlgebraicClosure ℚ)) * C (flatCone x p) :=
    funext fun p ↦ mul_comm _ _
  have hC : aeval (fun p : Coord n ↦ (C (flatCone x p) : MvPolynomial ι (AlgebraicClosure ℚ))) G =
      C (aeval (flatCone x) G) := by
    rw [aeval_def, aeval_def, eval₂_comp_left]
    congr 1
  change aeval (fun p : Coord n ↦ C (flatCone x p) * (X p.1 : MvPolynomial ι (AlgebraicClosure ℚ))) G = 0
  have h := aeval_mul_of_homog (fun k : ι ↦ (X k : MvPolynomial ι (AlgebraicClosure ℚ)))
    (fun p ↦ C (flatCone x p)) hG
  beta_reduce at h
  rw [e]
  refine h.trans (mul_eq_zero_of_left (hC.trans ?_) _)
  rw [h0, map_zero]
end GroundTheory.Heights₂.Heights.OrbitChartMax
