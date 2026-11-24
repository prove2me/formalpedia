-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_toFrac_eq_zero_5eaebcef54dc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:37.560979+00:00
-- url     : https://prove2.me/submissions/92f50d2b-a135-4a18-acdc-456c0912f75d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsFunFieldMulEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotMemOfNonZeroDivisor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
theorem _root_.solution {P : Ideal (MRing ι)} [P.IsPrime] {f : MRing ι} : toFrac P f = 0 ↔ f ∈ P := by
  rw [RingHom.comp_apply, ← map_zero (algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))),
    (IsFractionRing.injective (MRing ι ⧸ P) _).eq_iff, Ideal.Quotient.eq_zero_iff_mem]
end GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
