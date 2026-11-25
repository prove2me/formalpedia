-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_I_fsHerm_sum_c920ea789a43
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:15:08.302092+00:00
-- url     : https://prove2.me/submissions/65ab114d-48fd-4d35-a68b-5bcc68c48d6e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFlagGrassSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PHFlProdLinear
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_fsMultilin_apply_b7db3b48315c

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
theorem _root_.solution (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {α : Type} [Fintype α]
    (ℓ : Fin (n + 1) → α → ℤ) (x : α → K → ℤ) :
    I P (n + 1) (fun i => fsHerm ι (∑ p, ℓ i p • x p)) =
      ∑ r : Fin (n + 1) → α, (∏ i, (ℓ i (r i) : ℝ)) * I P (n + 1) (fun i => fsHerm ι (x (r i))) := by
  rw [← fsMultilin_apply hI hP, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.map_smul_univ (fsMultilin hI hP) (fun i => ℓ i (r i)) (fun i => x (r i)),
    fsMultilin_apply, zsmul_eq_mul, Int.cast_prod]
end GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear
