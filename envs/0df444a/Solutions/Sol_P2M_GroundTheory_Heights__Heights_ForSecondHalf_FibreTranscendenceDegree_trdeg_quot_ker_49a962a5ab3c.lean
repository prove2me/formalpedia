-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_trdeg_quot_ker_49a962a5ab3c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:12:06.946001+00:00
-- url     : https://prove2.me/submissions/f6db3553-a17e-4b0b-945a-4a9fa671a10d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIntDomainDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PEvalKerKrullDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PFibreMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_SemipositiveHeights_FibreDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ForSecondHalf
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.ForSecondHalf.FibreTranscendenceDegree
namespace GroundTheory.Heights₂.Heights.ForSecondHalf.FibreTranscendenceDegree
theorem _root_.solution {σ : Type} {M : Type} [CommRing M] [IsDomain M] (y : σ → M) :
    Algebra.trdeg ℤ (MvPolynomial σ ℤ ⧸ RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] M)) =
      Algebra.trdeg ℤ (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] M).range := by
  have hker : RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] M) =
      RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] M).rangeRestrict := by
    ext p
    simp [RingHom.mem_ker, Subtype.ext_iff]
  exact ((Ideal.quotientEquivAlgOfEq ℤ hker).trans
    (Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective _))).trdeg_eq
end GroundTheory.Heights₂.Heights.ForSecondHalf.FibreTranscendenceDegree
