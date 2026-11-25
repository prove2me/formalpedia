-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsNear_pow_card_le_norm_prod_4142eeda9e0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:12.889604+00:00
-- url     : https://prove2.me/submissions/941ab412-d219-4612-aff3-2dc3bf1b50ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRootsNear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Filter Topology
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace RootsNear
theorem _root_.solution (s : Multiset ℂ) (t₀ : ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ a ∈ s, ε ≤ dist a t₀) :
    ε ^ Multiset.card s ≤ ‖(s.map fun a => t₀ - a).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ, mul_comm]
    have h1 : ε ≤ ‖t₀ - a‖ := by
      rw [← dist_eq_norm, dist_comm]; exact h a (Multiset.mem_cons_self _ _)
    have h2 := ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))
    exact mul_le_mul h1 h2 (pow_nonneg hε _) (norm_nonneg _)
end RootsNear
end GroundTheory.Heights₂.Heights.HilbertSamuel
