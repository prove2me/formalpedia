-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_pow_eq_13112438b8ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:21:07.392642+00:00
-- url     : https://prove2.me/submissions/4299e313-a441-42fc-9c1d-e979edbf16ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_zero_eq_one_5ef25f86ec85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_mul_twistMod_032661586f67

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
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (c : ℤ) (n : ℕ) (I : Chart x) :
    twistMod k x c I ^ n = twistMod k x (n * c) I := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, twistMod_zero_eq_one]
  | succ n ih => rw [pow_succ, ih, twistMod_mul_twistMod]; push_cast; ring_nf
end GroundTheory.Heights₂.Heights.Kleiman
