-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_sum_332cef462e63
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:57:10.627635+00:00
-- url     : https://prove2.me/submissions/73ca18d7-2265-4f1c-b213-b2aa960a4f98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_add_23cf9d873983

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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution {ι : Type*} (s : Finset ι) {f N : ℕ} {H P : ι → RootRing f N}
    (h : ∀ i ∈ s, HasDD f N (H i) (P i)) : HasDD f N (∑ i ∈ s, H i) (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [HasDD, antisymmetrize]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact hasDD_add (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
end GroundTheory.Heights₂.Heights.RestTerms.Top
