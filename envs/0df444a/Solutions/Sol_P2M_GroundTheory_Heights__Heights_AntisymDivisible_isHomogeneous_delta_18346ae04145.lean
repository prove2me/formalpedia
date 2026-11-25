-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AntisymDivisible_isHomogeneous_delta_18346ae04145
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:35:47.682327+00:00
-- url     : https://prove2.me/submissions/7aeedadc-9304-4090-9c89-5324f6331459

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AntisymDivisible
variable {T : Type} [Fintype T] [DecidableEq T] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.AntisymDivisible
theorem _root_.solution : (antisymDelta T N).IsHomogeneous (antisymDegree T N) := by
  have h : (antisymDelta T N).IsHomogeneous (∑ τ : T, ∑ a : Fin N, ∑ b ∈ Finset.Ioi a, 1) := by
    unfold antisymDelta
    refine IsHomogeneous.prod _ _ _ fun τ _ => IsHomogeneous.prod _ _ _ fun a _ =>
      IsHomogeneous.prod _ _ _ fun b _ => ?_
    exact (isHomogeneous_X ℝ _).sub (isHomogeneous_X ℝ _)
  have e : (∑ τ : T, ∑ a : Fin N, ∑ b ∈ Finset.Ioi a, 1) = antisymDegree T N := by
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, antisymDegree]
    congr 1
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Ioi]
    rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N, Finset.sum_range_reflect (fun i => i) N,
      Finset.sum_range_id, Nat.choose_two_right]
  rwa [e] at h
end GroundTheory.Heights₂.Heights.AntisymDivisible
