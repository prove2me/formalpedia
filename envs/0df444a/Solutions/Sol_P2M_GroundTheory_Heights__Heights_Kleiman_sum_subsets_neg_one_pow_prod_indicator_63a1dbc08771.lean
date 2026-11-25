-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_sum_subsets_neg_one_pow_prod_indicator_63a1dbc08771
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:24:13.693871+00:00
-- url     : https://prove2.me/submissions/0763fb35-011f-4893-ac2f-fb86062fc7ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StSubsetDiffConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PSubsetDiffConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (n : ℕ) (a : Fin n → ℕ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) * ∏ i, (if i ∈ T then (1 : ℚ) else 0) ^ a i =
      ∏ i, (1 - (0 : ℚ) ^ a i) := by
  have h := Finset.prod_add (fun _ : Fin n => (1 : ℚ)) (fun i => -((0 : ℚ) ^ a i)) univ
  simp only [← sub_eq_add_neg, powerset_univ, prod_const_one, one_mul] at h
  rw [h]
  refine sum_congr rfl fun T _ => ?_
  rw [prod_neg, ← compl_eq_univ_sdiff, card_compl, Fintype.card_fin]
  congr 1
  rw [← prod_mul_prod_compl T]
  rw [prod_congr rfl (fun i hi => by rw [if_pos hi, one_pow]), prod_const_one, one_mul]
  exact prod_congr rfl fun i hi => by rw [if_neg (mem_compl.mp hi)]
end GroundTheory.Heights₂.Heights.Kleiman
