-- Prove2me | solution 1 for Reformulated.AutPerF.Bst.logFlat_twist
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:16.899266+00:00
-- url     : https://prove2.me/submissions/5667537e-0682-405a-903a-150b74ba5efc

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Theorems.Thm_Reformulated_AutPerF_Bst_mk_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.Bst
variable {p R}
namespace Reformulated.AutPerF.Bst
theorem _root_.solution (η : tateModule p R) (ϖ : PFlat p R) :
    logFlat (ϖ.twist η) = algebraMap _ _ (Bcris.logTeich η) + logFlat ϖ := by
  rw [← sub_eq_zero, logFlat, logFlat, ← (mk p R).commutes, ← map_add, ← map_sub, mk_eq_zero_iff]
  exact subset_span ⟨η, ϖ, rfl⟩
end Reformulated.AutPerF.Bst
