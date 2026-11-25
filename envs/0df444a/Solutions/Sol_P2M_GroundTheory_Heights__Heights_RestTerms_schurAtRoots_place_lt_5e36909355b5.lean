-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_schurAtRoots_place_lt_5e36909355b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:13:30.267938+00:00
-- url     : https://prove2.me/submissions/d0037137-89a9-4a87-9173-17c1fc285975

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchSchurAtRootsOfUnity

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
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution {r k : ℕ} (nu : Fin r → ℕ) (hanti : Antitone nu)
    (hsum : ∑ i, nu i = k) (i : Fin r) (hi : 1 ≤ nu i) : (i : ℕ) < k := by
  have h1 : (Iic i).card • 1 ≤ ∑ j ∈ Iic i, nu j :=
    Finset.card_nsmul_le_sum _ _ _ fun j hj => le_trans hi (hanti (Finset.mem_Iic.mp hj))
  have h2 : ∑ j ∈ Iic i, nu j ≤ ∑ j, nu j :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Fin.card_Iic, smul_eq_mul, mul_one] at h1
  omega
end GroundTheory.Heights₂.Heights.RestTerms
