-- Prove2me | solution 1 for ThreeSum.LightTernaryDivide.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:24:39.586461+00:00
-- url     : https://prove2.me/submissions/be04e488-98b6-489e-8b48-b4b9e6b43b10

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDivide
import Mathlib.Data.Int.Order.Lemmas
import Definitions.Def_Submission_ThreeSum_LightTernaryDivide
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_bounded_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryDivide
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryDivide
theorem _root_.solution {pMain pDivide Mo V fr : ℕ} {a q : ℤ} (hmain : P[pMain]? = some (body pDivide))
    (hdivide : P[pDivide]? = some LightOutputDecodeDivide.body) (μ : ℕ → ℤ) (F : Light.Emod.Pre lim Mo V fr)
    (ha : a.natAbs ≤ V) (heq : a = (Mo : ℤ) * q) (hd : d + 1 ≤ lim.depth) :
    Meets lim P pMain d [a, Mo, fr] μ (time V) (fun r μ' => r = q ∧ Kept μ μ' fr) :=
  by
  (obtain ⟨⟩ := _root_.id F)
  have hM : (0 : ℤ) < (Mo : ℤ) := by exact_mod_cast F.mod_pos
  have hn : (Mo : ℤ) ≠ 0 := ne_of_gt hM
  have habs : |a| ≤ (V : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast ha
  apply Meets.of_body hmain
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
    refine _root_.Light.Ends.iteIffThen (a < 0) (fun hneg => ?_) (fun hnonneg => ?_) ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightOutputDecodeDivide.budget]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightOutputDecodeDivide.budget] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightOutputDecodeDivide.budget] <;> omega)
    all_goals
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_
  · have hna : ((-a).toNat : ℤ) = -a := Int.toNat_of_nonneg (by omega)
    have hnav : (-a).toNat ≤ V := by
      have hab : -a ≤ (V : ℤ) := by omega
      omega
    have hc := LightOutputDecodeDivide.bounded_meets (d := d + 1) (a := (-a).toNat) (μ := μ) hdivide F hnav
    have hquot : (((-a).toNat / Mo : ℕ) : ℤ) = -q :=
      by
      rw [Int.natCast_ediv, hna, heq]
      rw [show -((Mo : ℤ) * q) = (Mo : ℤ) * (-q) by ring, Int.mul_ediv_cancel_left _ hn]
    have hqabs : |q| ≤ |a| := by
      rw [heq, abs_mul]
      have hMp : 1 ≤ |(Mo : ℤ)| := by rw [abs_of_pos hM]; exact_mod_cast F.mod_pos
      nlinarith [abs_nonneg q]
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      first
      | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hna,
              LightOutputDecodeDivide.budget]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hna, LightOutputDecodeDivide.budget] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hna, LightOutputDecodeDivide.budget] <;>
            omega)
      on_goal -1 => (rintro r μ' ⟨hr, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hrq : r = -q := hr.trans hquot
    have hqb := abs_le.mp (hqabs.trans habs)
    have hrb : |r| ≤ (V : ℤ) := by
      rw [hrq, abs_neg]
      exact hqabs.trans habs
    have hrbounds := abs_le.mp hrb
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen q ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrq,
              LightOutputDecodeDivide.budget]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hrq, LightOutputDecodeDivide.budget] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrq, LightOutputDecodeDivide.budget] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨rfl, hkeep⟩
  · have ha0 : 0 ≤ a := by omega
    have hpa : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha0
    have hpav : a.toNat ≤ V := by
      have hab : a ≤ (V : ℤ) := by omega
      omega
    have hc := LightOutputDecodeDivide.bounded_meets (d := d + 1) (a := a.toNat) (μ := μ) hdivide F hpav
    have hquot : ((a.toNat / Mo : ℕ) : ℤ) = q := by rw [Int.natCast_ediv, hpa, heq, Int.mul_ediv_cancel_left _ hn]
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      first
      | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hpa,
              LightOutputDecodeDivide.budget]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hpa, LightOutputDecodeDivide.budget] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hpa, LightOutputDecodeDivide.budget] <;>
            omega)
      on_goal -1 => (rintro r μ' ⟨hr, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    exact ⟨hr.trans hquot, hkeep⟩
end ThreeSum.LightTernaryDivide
