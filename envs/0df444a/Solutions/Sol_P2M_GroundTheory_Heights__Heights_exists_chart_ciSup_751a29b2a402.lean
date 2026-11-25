-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_chart_ciSup_751a29b2a402
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:40:40.538681+00:00
-- url     : https://prove2.me/submissions/761d443c-85aa-4f6b-8618-c47f8c364b60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenter
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterMemIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterDivSuppLemmas

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x)
    (v : FinitePlace (coordField x)) :
    ∃ c : (k : ι) → Fin (n k + 1), ∀ k, v (coordVec x k (c k)) = ⨆ i, v (coordVec x k i) ∧
      0 < ⨆ i, v (coordVec x k i) := by
  choose c hc using fun k ↦ exists_eq_ciSup_of_finite (f := fun i ↦ v (coordVec x k i))
  refine ⟨c, fun k ↦ ⟨hc k, ?_⟩⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (hx k)
  have hi' : coordVec x k i ≠ 0 := fun h ↦ hi (congrArg Subtype.val h)
  exact (FinitePlace.pos_iff.mpr hi').trans_le
    (le_ciSup (f := fun i ↦ v (coordVec x k i)) (Set.finite_range _).bddAbove i)
end GroundTheory.Heights₂.Heights
