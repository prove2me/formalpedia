-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_sum_833b8cb4f103
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:08:43.610406+00:00
-- url     : https://prove2.me/submissions/0293f4e7-5a58-489d-8a6d-d959bdc7fd03

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_add_c1cef20a7e70

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
theorem _root_.solution {ι : Type*} (s : Finset ι) (f N : ℕ) (H : ι → RootRing f N) :
    antisymmetrize f N (∑ i ∈ s, H i) = ∑ i ∈ s, antisymmetrize f N (H i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [antisymmetrize]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, antisymmetrize_add, ih]
end GroundTheory.Heights₂.Heights.RestTerms.Top
