-- Prove2me | solution 1 for ThreeSum.LightTernaryCarryCodes.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:42:08.994556+00:00
-- url     : https://prove2.me/submissions/ee7e9925-6dbf-43cc-b07a-288c9b2c7c86

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Theorems.Thm_ThreeSum_LightTernaryCarryCodes_table_meets
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCarryCodes
open Light TernarySignedDigits
set_option maxHeartbeats 2400000
set_option maxRecDepth 9000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
namespace ThreeSum.LightTernaryCarryCodes
theorem _root_.solution {pMain pPower pTable pRow pDecode pDivide J dst work : ℕ}
    (hmain : P[pMain]? = some (body pPower pTable)) (hpower : P[pPower]? = some LightNatPower.body)
    (htable : P[pTable]? = some (tableBody pRow)) (hrow : P[pRow]? = some (rowBody pDecode))
    (hdecode : P[pDecode]? = some (LightOutputDecodeDigits.body pDivide))
    (hdivide : P[pDivide]? = some LightOutputDecodeDivide.body) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 4 < lim.depth) (hsep : dst + 2 ^ J * (J + 1) ≤ work) (hspace : space work (2 ^ J) ≤ lim.space)
    (hword : (word J (2 ^ J) : ℤ) ≤ lim.word) :
    Meets lim P pMain d [J, dst, work] μ (time J) (fun r ν => r = (2 ^ J : ℕ) ∧ Table ν dst J (2 ^ J) ∧ Kept μ ν dst) :=
  by
  have hwork : work ≤ lim.space := by unfold space LightOutputDecodeDigits.space at hspace; omega
  have hQWord : ((2 ^ J : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word LightOutputDecodeDigits.word; omega : 2 ^ J ≤ word J (2 ^ J))).trans hword
  have hJWord : (J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word LightOutputDecodeDigits.word; omega : J ≤ word J (2 ^ J))).trans hword
  have h2Word : (2 : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word LightOutputDecodeDigits.word; omega : 2 ≤ word J (2 ^ J))).trans hword
  have hpow (i : ℕ) (hi : i ≤ J) : ((2 ^ i : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hi)).trans hQWord
  apply Meets.of_body hmain
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
        _root_.Light.Ends.callToThen ((LightNatPower.meets (d := d + 1) hpower μ hJWord hpow) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (LightNatPower.meets (d := d + 1) hpower μ hJWord hpow) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro Q ν ⟨hQ, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν
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
          ((table_meets (d := d + 1) (Q := 2 ^ J) (J := J) (dst := dst) (work := work) htable hrow hdecode hdivide hw
              (by omega) hsep hspace hword)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (table_meets (d := d + 1) (Q := 2 ^ J) (J := J) (dst := dst) (work := work) htable hrow hdecode hdivide hw
            (by omega) hsep hspace hword)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hQ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hQ] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hQ] <;> omega)
    on_goal -1 => (rintro ret ξ ⟨hret, hrows, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (2 ^ J : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hQ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hQ] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hQ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  exact ⟨rfl, hrows, hkeep⟩
end ThreeSum.LightTernaryCarryCodes
