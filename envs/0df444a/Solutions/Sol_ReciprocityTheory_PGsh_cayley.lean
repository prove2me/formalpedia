-- Prove2me | solution 1 for ReciprocityTheory.PGsh.cayley
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:49:14.740437+00:00
-- url     : https://prove2.me/submissions/0a863875-9f7f-4f4e-bf13-792d68ea22b6

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Theorems.Thm_ReciprocityTheory_PGsh_cayOp_linSub
import Theorems.Thm_ReciprocityTheory_PGsh_cayley_int_succ
import Theorems.Thm_ReciprocityTheory_PGsh_eval_one_cayOp_pow
import Theorems.Thm_ReciprocityTheory_PGsh_cayOp_map
import Theorems.Thm_ReciprocityTheory_PGsh_cayDet_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {n : ℕ}
namespace ReciprocityTheory.PGsh
theorem _root_.solution : CayleyStatement := by
  unfold CayleyStatement
  intro n R _ s
  rcases s with _ | t
  · rcases n with _ | m
    · simp [cayOp, cayMono]
    · have hd : (0 : Matrix (Fin (m + 1)) (Fin (m + 1)) R).det = 0 := Matrix.det_zero
      have h := cayOp_linSub (n := m + 1) (R := R) 0 1
      simp only [map_one, hd, map_zero, zero_mul] at h
      rw [pow_zero, h, Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos m)) (zero_add 0),
        zero_smul]
  · rw [← cayDet_map (n := n) (R := R), ← map_pow, cayOp_map, cayley_int_succ,
      eval_one_cayOp_pow, map_mul, map_pow, cayDet_map, map_C]
    simp [nsmul_eq_mul]
end ReciprocityTheory.PGsh
