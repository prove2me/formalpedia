-- Prove2me | solution 1 for P2M_Formalism_L2_FormalSeriesBounds_GmExArith_ge_pow__b134f1ece94e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:22:12.033949+00:00
-- url     : https://prove2.me/submissions/47df7e2a-067d-4309-9f35-514c33835fba

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGmExLem
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mul
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.GmExArith
open Formalism.L2.FormalSeriesBounds NumberField
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.GmExArith
theorem _root_.solution {r : ℝ} {a : C} (h : V.Ge r a) (k : ℕ) : V.Ge ((k : ℝ) * r) (a ^ k) := by
  induction k with
  | zero => rw [Nat.cast_zero, zero_mul, pow_zero]; exact VF.Ge.one
  | succ k ih =>
    rw [pow_succ]
    have := ih.mul h
    convert this using 1
    push_cast; ring
end Formalism.L2.FormalSeriesBounds.GmExArith
