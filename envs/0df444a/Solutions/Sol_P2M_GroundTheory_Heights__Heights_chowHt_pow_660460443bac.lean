-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_chowHt_pow_660460443bac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:33:44.460797+00:00
-- url     : https://prove2.me/submissions/30d7e9a2-2b76-4464-a6df-fc94c4d08c27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chowHeightConst_8b6933d50429


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
open MvPolynomial MeasureTheory NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (hMul : ChowHeightMul.Statement) (H : ArchData K n) {k : ℕ} (d : ℕ)
    {g : MvPolynomial (Fin k × Fin n) K} (hg : g ≠ 0) (m : ℕ) :
    chowHt H k (m * d) (g ^ m) = m * chowHt H k d g := by
  induction m with
  | zero =>
    rw [zero_mul, pow_zero, Nat.cast_zero, zero_mul, ← C_1]
    exact chowHeightConst K n k H 1 one_ne_zero
  | succ m ih =>
    rw [pow_succ, Nat.succ_mul, hMul K n H k _ _ _ _ (pow_ne_zero _ hg) hg, ih]
    push_cast
    ring
end GroundTheory.Heights₂.Heights
