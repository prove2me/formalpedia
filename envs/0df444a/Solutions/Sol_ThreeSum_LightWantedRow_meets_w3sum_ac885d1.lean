-- Prove2me | solution 1 for ThreeSum.LightWantedRow.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:21:26.720617+00:00
-- url     : https://prove2.me/submissions/512fd1cf-c860-4b18-9b1e-187a726be3be

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightWantedRow
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
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
open ThreeSum ThreeSum.LightWantedRow
open Light
set_option maxHeartbeats 900000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightWantedRow
theorem _root_.solution {pMain left src start n dst previous : ℕ} {μ : ℕ → ℤ} (hmain : P[pMain]? = some body)
    (hw : (lim.space : ℤ) ≤ lim.word) (hsrc : src + start + n ≤ dst) (hspace : dst + 2 * (previous + n) ≤ lim.space)
    (hleft : (left : ℤ) ≤ lim.word) (hvalues : ∀ t < n, |μ (src + start + t)| ≤ lim.word) :
    Meets lim P pMain d [left, src, start, n, dst, previous] μ (time n)
      (fun _ ν =>
        (∀ t < n, ν (dst + 2 * (previous + t)) = (left : ℤ) ∧ ν (dst + 2 * (previous + t) + 1) = μ (src + start + t)) ∧
          SameOutside μ ν (dst + 2 * previous) (2 * n)) :=
  by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ left src start n dst previous) n 112 ?start ?round ?done ?bound
  case start =>
    refine ⟨μ, by simp [update_frame_setLocal], ?_, SameOutside.refl⟩
    intro t ht
    omega
  case round =>
    rintro j _ hj _ ⟨ν, rfl, written, kept⟩
    have hread : ν (src + start + j) = μ (src + start + j) := kept _ (Or.inl (by omega))
    have hvalue := abs_le.mp (hvalues j hj)
    have hreadAfter : Function.update ν (dst + 2 * (previous + j)) (left : ℤ) (src + start + j) = μ (src + start + j) :=
      by rw [Function.update_of_ne (by omega), hread]
    have haddress : ((src : ℤ) + (start : ℤ) + (j : ℤ)).toNat = src + start + j := by omega
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + 2 * (previous + j)) (left : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + 2 * (previous + j) + 1) (μ (src + start + j) : ℤ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, haddress,
              hreadAfter]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [haddress, hreadAfter] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haddress, hreadAfter] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine
      ⟨by simp,
        Function.update (Function.update ν (dst + 2 * (previous + j)) (left : ℤ)) (dst + 2 * (previous + j) + 1)
          (μ (src + start + j)),
        by simp [update_frame_setLocal], ?_, ?_⟩
    · intro t ht
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
      · constructor
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact (written t ht).1
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact (written t ht).2
      · constructor
        · rw [Function.update_of_ne (by omega), Function.update_self]
        · rw [Function.update_self]
    · intro a ha
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact kept a ha
  case done =>
    rintro _ _ ⟨ν, rfl, written, kept⟩
    exact ⟨written, kept⟩
  case bound =>
    rintro j _ hj _ ⟨ν, rfl, _, _⟩
    simp
end ThreeSum.LightWantedRow
