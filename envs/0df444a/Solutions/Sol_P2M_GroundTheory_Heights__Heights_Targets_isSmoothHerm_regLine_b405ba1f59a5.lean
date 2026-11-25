-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_isSmoothHerm_regLine_b405ba1f59a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:55:35.860982+00:00
-- url     : https://prove2.me/submissions/037bcf1a-3ef2-4be0-bebe-31d79d41b8aa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_IsMultiHomogPlaneCoordinate
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_contDiffOn_regLog_bb6945e5f7c4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution {A : HermLine ι} (hA : IsSmoothHerm A) {s : MRing ι} {ε : ℝ} (hε : 0 < ε)
    {a : K → ℕ} (ha : ∀ k, A.a k = a k) (hs : IsMultiHomog s a) :
    IsSmoothHerm (regLine A s ε ha hs) :=
  Real.contDiff_exp.comp_contDiffOn (contDiffOn_regLog hA s hε).neg.neg
end GroundTheory.Heights₂.Heights.Targets
