-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitCurve_isHorizontal_orbitIdeal_fbfadf85b618
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:30:09.598818+00:00
-- url     : https://prove2.me/submissions/8b06cef7-b52a-48eb-b270-214815d4b796

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G Algebra
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitCurve
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.OrbitCurve
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) :
    Geo.IsHorizontal (ι := blockIdx n) (orbitIdeal x) := by
  ext a
  rw [Ideal.mem_comap, Ideal.mem_bot, orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker]
  change aeval _ (C a) = 0 ↔ a = 0
  rw [aeval_C]
  exact map_eq_zero_iff _ (RingHom.injective_int _)
end GroundTheory.Heights₂.Heights.OrbitCurve
