-- Prove2me | solution 1 for Reformulated.AutPerF.AcrisZero.factorial_mul_gamma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:28:47.691352+00:00
-- url     : https://prove2.me/submissions/b15f33e0-1df1-4dff-9896-cff9b99b3e5f

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap



set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
open Reformulated Reformulated.AutPerF
universe u v w
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.AcrisZero
namespace Reformulated.AutPerF.AcrisZero
theorem _root_.solution (n : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    (n ! : AcrisZero p R) * gamma n x hx = algebraMap (Ainf p R) _ x ^ n := by
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast, coe_gamma,
    AinfInv.gamma, Subalgebra.coe_algebraMap]
  rw [Algebra.smul_def, ← map_natCast (algebraMap ℚ (AinfInv p R)), ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero _), map_one, one_mul]
end Reformulated.AutPerF.AcrisZero
