-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_prod_X_3f51a0201239
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:33:45.623111+00:00
-- url     : https://prove2.me/submissions/24b6bdac-9be9-42a5-864d-fd7c65bcb6d6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_IsFrameOverLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_X_single_975289589ee1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_mul_0d39b8f19b1f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_one_0a1e8350c35d


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
open scoped Matrix
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution (c : (k : K) → ι k) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι)) (fun _ => 1) := by
  classical
  have key : ∀ s : Finset K,
      IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι)) (fun k => if k ∈ s then 1 else 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.notMem_empty, if_false]
      exact isMultiHomog_one
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      convert isMultiHomog_mul (isMultiHomog_X_single (ι := ι) ⟨a, c a⟩) ih using 1
      funext k
      by_cases hk : k = a
      · subst hk; simp [ha]
      · simp [hk]
  simpa using key Finset.univ
end GroundTheory.Heights₂.Heights.LowerBoundFree
