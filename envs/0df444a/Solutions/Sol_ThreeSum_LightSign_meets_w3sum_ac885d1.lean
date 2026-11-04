-- Prove2me | solution 1 for ThreeSum.LightSign.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:36:08.515221+00:00
-- url     : https://prove2.me/submissions/120c9267-b6e1-47cc-aa5e-219fbbfa705a

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightSign
import Theorems.Thm_Light_Limits_Addr_abs_le
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
open ThreeSum ThreeSum.LightSign
open Light
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSign
theorem _root_.solution {pMain e d : ℕ} {x : ℤ} {μ : ℕ → ℤ} (hmain : P[pMain]? = some body)
    (hw : (lim.space : ℤ) ≤ lim.word) (he : e ≤ lim.space) (hvalue : |x| ≤ lim.word) :
    Meets lim P pMain d [x, e] μ (time e) (fun r μ' => r = (-1 : ℤ) ^ e * x ∧ μ' = μ) :=
  by
  have hb (j : ℕ) : |(-1 : ℤ) ^ j * x| ≤ lim.word := by simpa only [abs_mul, abs_neg_one_pow, one_mul] using hvalue
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.for (Inv μ x e) e 10 ?start ?round ?done ?bound (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega)))
  case start => simp [Inv, update_frame_setLocal]
  case round =>
    rintro j _ hj _ rfl
    have hnext := abs_le.mp (hb (j + 1))
    have htoggle : (0 : ℤ) - ((-1 : ℤ) ^ j * x) = (-1 : ℤ) ^ (j + 1) * x :=
      by
      rw [pow_succ]
      ring
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen ((-1 : ℤ) ^ (j + 1) * x) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, htoggle]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [htoggle] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, htoggle] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    constructor
    · simp
    · simp [Inv, update_frame_setLocal]
  case done =>
    rintro _ _ rfl
    exact ⟨by simp, rfl⟩
  case bound =>
    rintro j _ hj _ rfl
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightSign
