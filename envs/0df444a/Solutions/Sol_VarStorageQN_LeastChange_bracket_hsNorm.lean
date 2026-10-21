-- Prove2me | solution 1 for VarStorageQN.LeastChange.bracket_hsNorm
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:28:41.231488+00:00
-- url     : https://prove2.me/submissions/0bdc6dea-6f2d-4482-be66-9a8f4065b021

import Mathlib
import Definitions.Def_VarStorageQN_LeastChange_HilbertSchmidt
import Definitions.Def_VarStorageQN_LeastChange_Bracket

set_option autoImplicit false
open InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace
open VarStorageQN.LeastChange

namespace VSQhelp
open VarStorageQN.LeastChange

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem parseval {ι : Type*} (b : HilbertBasis ι ℝ H) (x : H) :
    HasSum (fun i => ⟪x, b i⟫_ℝ ^ 2) (‖x‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner x x
  rw [real_inner_self_eq_norm_sq] at h
  have e : (fun i => ⟪x, b i⟫_ℝ ^ 2) = fun i => ⟪x, b i⟫_ℝ * ⟪b i, x⟫_ℝ := by
    funext i
    rw [real_inner_comm (b i) x, sq]
  rw [e]; exact h

theorem hasSum_bracket {ι : Type*} (b : HilbertBasis ι ℝ H) (u v : H) :
    HasSum (fun i => ‖bracket u v (b i)‖ ^ 2) (‖u‖ ^ 2 * ‖v‖ ^ 2) := by
  have h := (parseval b v).mul_left (‖u‖ ^ 2)
  have e : (fun i => ‖bracket u v (b i)‖ ^ 2) = fun i => ‖u‖ ^ 2 * ⟪v, b i⟫_ℝ ^ 2 := by
    funext i
    rw [bracket, rankOne_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  rw [e]; exact h

theorem hsSummable_bracket {ι : Type*} (b : HilbertBasis ι ℝ H) (u v : H) :
    HSSummable b (bracket u v) := (hasSum_bracket b u v).summable

theorem hsNorm_bracket {ι : Type*} (b : HilbertBasis ι ℝ H) (u v : H) :
    hsNorm b (bracket u v) = ‖u‖ * ‖v‖ := by
  unfold hsNorm
  rw [(hasSum_bracket b u v).tsum_eq, ← mul_pow]
  exact Real.sqrt_sq (by positivity)

end VSQhelp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem solution {ι : Type*} (b : HilbertBasis ι ℝ H) (u v : H) :
    HSSummable b (bracket u v) ∧
    hsNorm b (bracket u v) = ‖bracket u v‖ ∧
    ‖bracket u v‖ = ‖u‖ * ‖v‖ := by
  refine ⟨VSQhelp.hsSummable_bracket b u v, ?_, norm_rankOne u v⟩
  rw [VSQhelp.hsNorm_bracket, norm_rankOne]
