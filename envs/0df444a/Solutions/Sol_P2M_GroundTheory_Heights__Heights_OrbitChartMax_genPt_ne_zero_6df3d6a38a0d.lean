-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMax_genPt_ne_zero_6df3d6a38a0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:43.724648+00:00
-- url     : https://prove2.me/submissions/e041fea8-f6cd-4756-86f9-edd79fa6267c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMax
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_genPt_eq_zero_iff_c5b571538e68

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
theorem _root_.solution {p : Coord n} (hp : (X p : MvPolynomial (Coord n) ℤ) ∉ V) : genPt V p ≠ 0 := by
  have h := (aeval_genPt_eq_zero_iff V (X p)).not.mpr hp
  rwa [aeval_X] at h
end GroundTheory.Heights₂.Heights.OrbitChartMax
