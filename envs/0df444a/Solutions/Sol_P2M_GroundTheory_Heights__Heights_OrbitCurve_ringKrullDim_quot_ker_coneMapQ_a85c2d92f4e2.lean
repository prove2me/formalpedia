-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitCurve_ringKrullDim_quot_ker_coneMapQ_a85c2d92f4e2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:16:02.533453+00:00
-- url     : https://prove2.me/submissions/f113aff8-149b-413c-a47d-36ccbbffb4f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_trdeg_range_coneMapQ_87f5e893117f
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_eq_trdeg


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
namespace GroundTheory.Heights₂.Heights.OrbitCurve
theorem _root_.solution {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    ringKrullDim (MvPolynomial (Coord n) ℚ ⧸ RingHom.ker (coneMapQ x)) = Fintype.card ι := by
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange (coneMapQ x)).toRingEquiv]
  have : Algebra.FiniteType ℚ (coneMapQ x).range :=
    Algebra.FiniteType.of_surjective (coneMapQ x).rangeRestrict (coneMapQ x).rangeRestrict_surjective
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg ℚ, trdeg_range_coneMapQ hx]
  simp
end GroundTheory.Heights₂.Heights.OrbitCurve
