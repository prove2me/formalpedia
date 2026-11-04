-- Prove2me | solution 1 for ThreeSum.LightSwitch.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:22:49.650036+00:00
-- url     : https://prove2.me/submissions/35212420-d10a-4a10-9da9-c9a739903154

import Definitions.Def_Submission_ThreeSum_LightSwitchBounds
import Definitions.Def_Submission_ThreeSum_LightSwitchScalar
import Definitions.Def_Submission_ThreeSum_LightSwitch
import Theorems.Thm_ThreeSum_LightSwitch_test_safe
import Theorems.Thm_ThreeSum_LightSwitch_test_holds_iff
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Ends_whileBlock
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightSwitch_at_accepts
import Theorems.Thm_ThreeSum_LightSwitch_before_rejects
import Theorems.Thm_ThreeSum_LightSwitch_index_le_residual
import Theorems.Thm_ThreeSum_Switch_mem_candidates
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.Switch.mem_candidates
set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitch
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {μ : ℕ → ℤ} {J j r q d : ℕ}
namespace ThreeSum.LightSwitch
theorem _root_.solution {p : ℕ} (hp : P[p]? = some body) (hj : j ≤ J) (hne : (Switch.candidates J j r).Nonempty)
    (hword : (word J r : ℤ) ≤ lim.word) :
    Meets lim P p d [J, j, r] μ (time r) (fun result ν => result = (Switch.switchIndex J j r : ℤ) ∧ ν = μ) :=
  by
  have hindex := index_le_residual hne
  have hbase : J + r + 1001 ≤ word J r := Nat.le_self_pow (by decide : (64 : ℕ) ≠ 0) _
  have hlinear : ((J + r + 1001 : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hbase).trans hword
  apply Meets.of_body hp
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
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
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.next (50 * Switch.switchIndex J j r + 60)
      (Ends.whileBlock (fun i σ => σ = ⟨frame [(J : ℤ), j, r, i], μ⟩) (Switch.switchIndex J j r) (by simp) ?round ?done
        (by
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, test]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [test] <;>
                first
                | omega
                | (ring_nf; omega))))
      (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, test]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [test] <;>
            first
            | omega
            | (ring_nf; omega)))
  case round =>
    rintro i _ hi rfl
    have hle : i ≤ r := by omega
    refine
      ⟨test_safe hj hle hword, (test_holds_iff hj).mpr (before_rejects hne hi), by
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega), ?_⟩
    simp [update_frame_setLocal]
  case done =>
    rintro _ rfl
    refine ⟨test_safe hj hindex hword, ?_, ?_⟩
    · rw [test_holds_iff hj]
      exact not_lt_of_ge (at_accepts hne)
    · focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.setToThen (Switch.switchIndex J j r) ?_ ?_ ?_
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
      exact ⟨rfl, rfl⟩
end ThreeSum.LightSwitch
