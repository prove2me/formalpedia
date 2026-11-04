-- Prove2me | solution 1 for ThreeSum.LightTernaryEulerRow.fill_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:31.611371+00:00
-- url     : https://prove2.me/submissions/81112cb1-1cc2-4efc-a0dd-ab820ace23ca

import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedSum
import Definitions.Def_Submission_ThreeSum_LightTernaryDivide
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerRow
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_abs_le
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEulerRow
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryEulerRow
theorem _root_.solution {pMain pRow pSum pDivide pNaturalDivide ws ks table N pcount Mo V fr U dst : ℕ} {q : ℤ}
    (hmain : P[pMain]? = some (fillBody pRow)) (hrow : P[pRow]? = some (body pSum pDivide))
    (hsum : P[pSum]? = some LightTernaryWeightedSum.body)
    (hdivide : P[pDivide]? = some (LightTernaryDivide.body pNaturalDivide))
    (hnatural : P[pNaturalDivide]? = some LightOutputDecodeDivide.body) (μ : ℕ → ℤ) (weights keys : ℕ → ℕ) (f : ℕ → ℤ)
    (F : Light.Emod.Pre lim Mo V fr) (hws : ws + N ≤ lim.space) (hks : ks + N ≤ lim.space)
    (htable : table + pcount ≤ lim.space) (hweights : ∀ i < N, μ (ws + i) = (weights i : ℤ))
    (hkeys : ∀ i < N, μ (ks + i) = (keys i : ℤ)) (hrange : ∀ i < N, keys i < pcount)
    (hread : ∀ i < N, μ (table + keys i) = f (keys i)) (hweight : ∀ i < N, weights i ≤ 2)
    (hvalue : ∀ i < N, |f (keys i)| ≤ U) (hV : 2 * (N + 1) * U ≤ V)
    (hEuler : LightTernaryWeightedSum.sum weights keys f N = (Mo : ℤ) * q) (hdst : dst < fr) (hd : d + 3 ≤ lim.depth) :
    Meets lim P pMain d [ws, ks, table, N, pcount, Mo, fr, dst] μ (fillTime N V)
      (fun r μ' => r = q ∧ μ' dst = q ∧ ∀ a < fr, a ≠ dst → μ' a = μ a) :=
  by
  (obtain ⟨⟩ := _root_.id F)
  have hsumAbs := LightTernaryWeightedSum.sum_abs_le weights keys f hweight hvalue (j := N) le_rfl
  have hnum : |LightTernaryWeightedSum.sum weights keys f N| ≤ (V : ℤ) :=
    by
    have hc : 2 * N * (U : ℤ) ≤ (V : ℤ) :=
      by
      have hb : 2 * N * U ≤ V := (Nat.mul_le_mul_right U (by omega : 2 * N ≤ 2 * (N + 1))).trans hV
      exact_mod_cast hb
    exact hsumAbs.trans hc
  have hq : |q| ≤ (V : ℤ) :=
    by
    have hM : 1 ≤ |(Mo : ℤ)| := by
      rw [abs_of_nonneg (Int.natCast_nonneg Mo)]
      exact_mod_cast F.mod_pos
    rw [hEuler, abs_mul] at hnum
    nlinarith [abs_nonneg q]
  have hqb := abs_le.mp hq
  have hcall :=
    meets (d := d + 1) hrow hsum hdivide hnatural μ weights keys f F hws hks htable hweights hkeys hrange hread hweight
      hvalue hV hEuler (by omega)
  apply Meets.of_body hmain
  unfold fillBody fillTime
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
    | refine _root_.Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, LightTernaryWeightedSum.time,
            LightTernaryDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, LightTernaryWeightedSum.time, LightTernaryDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, LightTernaryWeightedSum.time,
            LightTernaryDivide.time] <;>
          omega)
    on_goal -1 => (rintro result ν ⟨hr, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.storeToThen dst q ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr, time, LightTernaryWeightedSum.time,
            LightTernaryDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hr, time, LightTernaryWeightedSum.time, LightTernaryDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr, time, LightTernaryWeightedSum.time,
            LightTernaryDivide.time] <;>
          omega)
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
    refine _root_.Light.Ends.setToThen q ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr, time, LightTernaryWeightedSum.time,
            LightTernaryDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hr, time, LightTernaryWeightedSum.time, LightTernaryDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr, time, LightTernaryWeightedSum.time,
            LightTernaryDivide.time] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨rfl, by simp, ?_⟩
  intro a ha hne
  change Function.update ν dst q a = μ a
  rw [Function.update_of_ne hne]
  exact hkeep a ha
end ThreeSum.LightTernaryEulerRow
