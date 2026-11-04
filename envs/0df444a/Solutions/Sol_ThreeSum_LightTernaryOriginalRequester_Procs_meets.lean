-- Prove2me | solution 1 for ThreeSum.LightTernaryOriginalRequester.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:02.593589+00:00
-- url     : https://prove2.me/submissions/741e26a4-07b5-4acf-bd5c-3350494b2967

import Definitions.Def_Submission_ThreeSum_LightTernaryCarryApply
import Definitions.Def_Submission_ThreeSum_LightTernaryOriginalRequester
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightTernaryCarryApply_meets
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_5d4b5ec466dc091a
import Theorems.Thm_ThreeSum_TernarySignedReduction_shiftOne_cast
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryOriginalRequester
open Light TernarySignedDigits TernarySignedReduction
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryOriginalRequester
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ} {U radix J dst carry work : ℕ} (a : ℤ)
    (c : CarryWord J) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 3 < lim.depth) (hb : 1 < radix) (hA : |a| ≤ (U : ℤ))
    (hcarryBefore : carry + J + 1 ≤ dst) (hsep : dst + J + 2 ≤ work)
    (hspace : LightTernarySignedRow.space work (3 * U) ≤ lim.space)
    (hword : (LightTernarySignedRow.word (3 * U) radix J : ℤ) ≤ lim.word)
    (hcarry : ∀ k ≤ J, μ (carry + k) = carryAt c (J - k)) :
    Meets lim P pMain d [a, U, radix, J, dst, carry, work] μ (time J U)
      (fun _ ν => LightTernarySignedRow.Row ν dst J (requesterRaw U radix J a c) ∧ Kept μ ν dst) :=
  by
  have hs := shiftOne_cast hA
  have hbounds := abs_le.mp hA
  have hU : (0 : ℤ) ≤ U := by positivity
  have hv : shiftOne U a ≤ 3 * U := by exact_mod_cast (by omega : (shiftOne U a : ℤ) ≤ 3 * U)
  have hwork : work ≤ lim.space :=
    by
    unfold LightTernarySignedRow.space LightOutputDecodeDigits.space at hspace
    omega
  have hB : (4 * (radix : ℤ) + 8) ≤ lim.word :=
    by
    have hh : 4 * radix + 8 ≤ LightTernarySignedRow.word (3 * U) radix J :=
      by
      unfold LightTernarySignedRow.word LightOutputDecodeDigits.word
      omega
    have hhZ : 4 * (radix : ℤ) + 8 ≤ (LightTernarySignedRow.word (3 * U) radix J : ℤ) := by exact_mod_cast hh
    exact hhZ.trans hword
  apply Meets.of_body S.main
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((S.row.meets (d := d + 1) (μ := μ) (J := J) (radix := radix) (dst := dst) (work := work) (V := 3 * U)
              (value := shiftOne U a) (offset := U) (x := a) (sign := (1 : ℤ)) (tag0 := (1 : ℤ)) (tag1 := (1 : ℤ)) hw
              (by omega) hb.le hv (by omega) (hA.trans (by omega)) (by omega) (by norm_num) (by norm_num) (by norm_num)
              hsep hspace hword)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (S.row.meets (d := d + 1) (μ := μ) (J := J) (radix := radix) (dst := dst) (work := work) (V := 3 * U)
            (value := shiftOne U a) (offset := U) (x := a) (sign := (1 : ℤ)) (tag0 := (1 : ℤ)) (tag1 := (1 : ℤ)) hw
            (by omega) hb.le hv (by omega) (hA.trans (by omega)) (by omega) (by norm_num) (by norm_num) (by norm_num)
            hsep hspace hword)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernarySignedRow.time,
            LightTernaryCarryApply.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernarySignedRow.time, LightTernaryCarryApply.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernarySignedRow.time,
            LightTernaryCarryApply.time] <;> omega)
    on_goal -1 => (rintro r ν ⟨hread, ht0, ht1, hkeep1⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hcRead : ∀ k ≤ J, ν (carry + k) = carryAt c (J - k) :=
    by
    intro k hk
    rw [hkeep1 _ (by omega), hcarry k hk]
  have hARead : ∀ k < J, ν (dst + k) = (digit radix (shiftOne U a) (J - 1 - k) : ℤ) :=
    by
    intro k hk
    rw [hread k hk, one_mul]
    have hj : J - 1 - k < J := by omega
    have he := OutputDecodeOrder.indices_getD_reverse radix J (shiftOne U a) hj
    rw [show J - 1 - (J - 1 - k) = k by omega] at he
    rw [he]
    rfl
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightTernaryCarryApply.meets (d := d + 1) (μ := ν) (U := U) (radix := radix) (J := J) (dst := dst) (carry :=
              carry) S.correction S.linear a c hw (by omega) hb (Or.inl hcarryBefore) (by omega) hB hARead hcRead ht0
              ht1)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightTernaryCarryApply.meets (d := d + 1) (μ := ν) (U := U) (radix := radix) (J := J) (dst := dst) (carry :=
            carry) S.correction S.linear a c hw (by omega) hb (Or.inl hcarryBefore) (by omega) hB hARead hcRead ht0 ht1)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernarySignedRow.time,
            LightTernaryCarryApply.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernarySignedRow.time, LightTernaryCarryApply.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernarySignedRow.time,
            LightTernaryCarryApply.time] <;> omega)
    on_goal -1 => (rintro r' ξ ⟨hrow, hkeep2⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨hrow, ?_⟩
  intro i hi
  exact (hkeep2 i hi).trans (hkeep1 i hi)
end Procs
end ThreeSum.LightTernaryOriginalRequester
