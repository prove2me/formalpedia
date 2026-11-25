-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitCurve_isPrime_orbitIdeal_50bb33dec3b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:12:24.981997+00:00
-- url     : https://prove2.me/submissions/7468b927-5568-4db2-be6c-d096c5dce054

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
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) : (orbitIdeal x).IsPrime :=
  RingHom.ker_isPrime _
end GroundTheory.Heights₂.Heights.OrbitCurve
