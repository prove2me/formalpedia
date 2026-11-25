-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_prod_fin_sub_eq_factorial_629ffefd5a56
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:13:30.121204+00:00
-- url     : https://prove2.me/submissions/6c0d88fb-902e-40a7-bcb4-d15d6b532f70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableEqCardMonotone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHookTableauCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (l : ℕ) : ∏ j : Fin l, (l - (j : ℕ)) = l.factorial := by
  rw [Fin.prod_univ_eq_prod_range (fun j => l - j) l,
    ← Finset.prod_range_reflect (fun j => l - j) l]
  have : ∀ j ∈ Finset.range l, l - (l - 1 - j) = j + 1 := by
    intro j hj
    have := Finset.mem_range.1 hj
    omega
  rw [Finset.prod_congr rfl this, Finset.prod_range_add_one_eq_factorial]
end GroundTheory.Heights₂.Heights.RestTerms
