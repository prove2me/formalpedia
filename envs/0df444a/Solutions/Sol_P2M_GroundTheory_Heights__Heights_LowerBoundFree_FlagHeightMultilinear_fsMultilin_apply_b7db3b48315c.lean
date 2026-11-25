-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_fsMultilin_apply_b7db3b48315c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:41:19.216635+00:00
-- url     : https://prove2.me/submissions/cb0f6ad6-ecc9-42ac-803e-604ff307a8bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFlagGrassSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PHFlProdLinear

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear
theorem _root_.solution (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) (v : Fin (n + 1) → K → ℤ) :
    fsMultilin hI hP v = I P (n + 1) (fun i => fsHerm ι (v i)) := rfl
end GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear
