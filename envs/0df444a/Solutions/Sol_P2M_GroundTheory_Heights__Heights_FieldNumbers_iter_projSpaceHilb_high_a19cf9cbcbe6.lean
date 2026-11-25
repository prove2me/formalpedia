-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_high_a19cf9cbcbe6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:13:30.123975+00:00
-- url     : https://prove2.me/submissions/7809bfc6-c385-42dc-aede-8cd144d11797

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPNProduct
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_backwardDifference_eq_zero_of_eventually_const_cf126017d8d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_top_c3fbe0f74289

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (N : ℕ) : ∀ i s : ℕ,
    diff1^[N + 1 + i] (projSpaceHilb N) ((s : ℤ) + ((N + 1 + i : ℕ) : ℤ)) = 0 := by
  intro i
  induction i with
  | zero =>
    intro s
    have hN : ∀ s : ℕ, diff1^[N] (projSpaceHilb N) ((s : ℤ) + (N : ℤ)) = 1 := fun s =>
      iter_projSpaceHilb_top N _ (by omega)
    have e : (s : ℤ) + ((N + 1 + 0 : ℕ) : ℤ) = s + ((N : ℤ) + 1) := by push_cast; ring
    rw [e, show N + 1 + 0 = N + 1 from rfl, Function.iterate_succ_apply']
    exact backwardDifference_eq_zero_of_eventually_const hN s
  | succ i ih =>
    intro s
    rw [show N + 1 + (i + 1) = (N + 1 + i) + 1 by omega, Function.iterate_succ_apply',
      Nat.cast_add_one]
    exact backwardDifference_eq_zero_of_eventually_const ih s
end GroundTheory.Heights₂.Heights.FieldNumbers
