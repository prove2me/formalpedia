-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KAlt_prod_sub_eq_prod_factorial_80b5f99ca249
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:00:33.480121+00:00
-- url     : https://prove2.me/submissions/3dd61bf3-3364-4573-a82c-9cb19bf14413

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltFrob

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
open Finset
open GroundTheory.Heights₂.Heights.KAlt
namespace GroundTheory.Heights₂.Heights.KAlt
theorem _root_.solution : ∀ r : ℕ,
    (∏ a : Fin r, ∏ b : Fin r, if a < b then ((b : ℕ) : ℚ) - ((a : ℕ) : ℚ) else 1) =
      ∏ a : Fin r, (((r - 1 - (a : ℕ)).factorial : ℕ) : ℚ)
  | 0 => by simp
  | r + 1 => by
    have h0 : (∏ b : Fin (r + 1), if (0 : Fin (r + 1)) < b
        then (((b : ℕ) : ℚ) - (((0 : Fin (r + 1)) : ℕ) : ℚ)) else 1) = (r.factorial : ℚ) := by
      rw [Fin.prod_univ_succ]
      simp only [lt_self_iff_false, if_false, Fin.succ_pos, if_true, one_mul, Fin.val_succ,
        Fin.val_zero, Nat.cast_zero, sub_zero]
      push_cast
      rw [Fin.prod_univ_eq_prod_range (fun i => ((i : ℚ) + 1)) r]
      exact_mod_cast Finset.prod_range_add_one_eq_factorial r
    have hs : ∀ a : Fin r, (∏ b : Fin (r + 1), if a.succ < b
        then (((b : ℕ) : ℚ) - ((a.succ : ℕ) : ℚ)) else 1) =
        ∏ b : Fin r, if a < b then (((b : ℕ) : ℚ) - ((a : ℕ) : ℚ)) else 1 := by
      intro a
      rw [Fin.prod_univ_succ]
      simp only [Fin.not_lt_zero, if_false, one_mul, Fin.succ_lt_succ_iff, Fin.val_succ]
      refine prod_congr rfl fun b _ => ?_
      split_ifs
      · push_cast; ring
      · rfl
    rw [Fin.prod_univ_succ, h0, prod_congr rfl (fun a _ => hs a), solution r,
      Fin.prod_univ_succ]
    congr 1
    all_goals first
      | (refine prod_congr rfl fun a _ => ?_
         congr 2
         simp only [Fin.val_succ]
         omega)
      | simp
end GroundTheory.Heights₂.Heights.KAlt
