-- Prove2me | solution 1 for ThreeSum.LightTernaryTensorScatter.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:04:55.205837+00:00
-- url     : https://prove2.me/submissions/0d88a5b8-f2e8-4550-9131-33f8696fc67e

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryTensorScatter
import Theorems.Thm_ThreeSum_LightTernaryTensorScatter_address_injective
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryTensorScatter
open Light
set_option maxHeartbeats 1800000
namespace ThreeSum.LightTernaryTensorScatter
theorem _root_.solution {lim : Limits} {P : Program} {p d src dst n W q : ℕ} (hmain : P[p]? = some body) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hW : 0 < W) (hq : q < W) (hsrc : src + n ≤ lim.space)
    (hdst : dst + n * W ≤ lim.space) (hsep : Apart src n dst (n * W)) (hWWord : (W : ℤ) ≤ lim.word)
    (hnWord : (n : ℤ) ≤ lim.word) :
    Meets lim P p d [src, dst, n, W, q] μ (time n)
      (fun _ ν => (∀ j < n, ν (dst + j * W + q) = μ (src + j)) ∧ (∀ x, (∀ j < n, x ≠ dst + j * W + q) → ν x = μ x)) :=
  by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ src dst n W q) n 52 ?_ ?_ ?_ ?_
  · refine ⟨μ, ?_, ?_, ?_⟩
    · simp [update_frame_setLocal]
    · intro j hj; omega
    · intro x hx; rfl
  · rintro i _ hi _ ⟨ν, rfl, hwrite, hkeep⟩
    have hiW : i * W + q < n * W :=
      by
      have := Nat.mul_le_mul_right W (by omega : i + 1 ≤ n)
      nlinarith
    have hread : ν (src + i) = μ (src + i) := by
      apply hkeep
      intro j hj
      have hjW : j * W + q < n * W :=
        by
        have := Nat.mul_le_mul_right W (by omega : j + 1 ≤ n)
        nlinarith
      omega
    have hprodNonneg : 0 ≤ (i : ℤ) * W := by positivity
    have hprodWord : (i : ℤ) * W ≤ lim.word :=
      by
      have hh : i * W ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (i : ℤ) * W ≤ lim.space).trans hw
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + i * W + q) (μ (src + i)) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hread]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hread] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp, Function.update ν (dst + i * W + q) (μ (src + i)), by simp [update_frame_setLocal], ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne]
        · exact hwrite j hj
        · intro he
          have := (address_injective hq hq (by omega : j * W + q = i * W + q)).1
          omega
      · simp
    · intro x hx
      rw [Function.update_of_ne (hx i (by omega))]
      exact hkeep x (by intro j hj; exact hx j (by omega))
  · rintro σ hcounter ⟨ν, rfl, hwrite, hkeep⟩
    exact ⟨hwrite, hkeep⟩
  · rintro i _ hi _ ⟨ν, rfl, hwrite, hkeep⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightTernaryTensorScatter
