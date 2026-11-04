-- Prove2me | solution 1 for ThreeSum.LightFixedRadixDictionary.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:51:05.538197+00:00
-- url     : https://prove2.me/submissions/5fde1bd4-ffaa-4a2b-8659-a829992a8e45

import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Definitions.Def_WeightedCache3SUM_Alias_4b4040d8de1fb856
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightFixedRadixDictionary
open Light RadixKeyLists
variable {lim : Limits}
set_option maxHeartbeats 1400000
namespace ThreeSum.LightFixedRadixDictionary
theorem _root_.solution (xs : List ℤ) {base dst p U J d : ℕ} (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase : base + xs.length ≤ dst) (hm : 0 < xs.length) (hbound : ∀ x ∈ xs, |x| ≤ (U : ℤ))
    (hspace : LightRadixKeys.space dst xs.length J ≤ lim.space) (hword : (LightRadixKeys.word p U J : ℤ) ≤ lim.word)
    (hd : d + J + 3 ≤ lim.depth) :
    Meets lim (program xs) 4 d [base, dst, J, p] μ (time xs J)
      (fun r ν =>
        r = ((dst + LightRadixKeys.offset xs.length J : ℕ) : ℤ) ∧
          ν (dst + LightRadixKeys.offset xs.length J) = ((xs.length ^ J : ℕ) : ℤ) ∧
            Seg ν (dst + LightRadixKeys.offset xs.length J + 1) (values (p : ℤ) xs J) ∧ Kept μ ν base) :=
  by
  have hdst : dst ≤ lim.space := by unfold LightRadixKeys.space at hspace; omega
  have hU : (U : ℤ) ≤ lim.word :=
    by
    have h : U ≤ LightRadixKeys.word p U J := by unfold LightRadixKeys.word LightRadixRows.word; omega
    exact (Int.ofNat_le.mpr h).trans hword
  have hv : ∀ x ∈ xs, |x| ≤ lim.word := fun x hx => (hbound x hx).trans hU
  have ht :=
    LightSignedFiniteTable.meets (P := program xs) (d := d + 1)
      (by rfl : (program xs)[0]? = some (LightSignedFiniteTable.body xs)) base μ hw (by omega) hv
  apply Meets.of_body (by rfl : (program xs)[4]? = some (body 0 1))
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
    first
    | refine _root_.Light.Ends.callToThen (ht _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen ht ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightRadixKeys.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightRadixKeys.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightRadixKeys.time] <;> omega)
    on_goal -1 => (rintro size μ₁ ⟨hsize, hlocal, hkeepTable⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hk :=
    LightRadixKeys.meets (P := program xs) (pMain := 1) (pRows := 2) (pAffine := 3) (src := base) (dst := dst) (p := p)
      (U := U) rfl rfl rfl xs hw hbase hm hbound J (d + 1) μ₁ hspace hword (by omega) hlocal
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
    | refine _root_.Light.Ends.callToThen (hk _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hk ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsize, LightRadixKeys.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hsize, LightRadixKeys.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsize, LightRadixKeys.time] <;> omega)
    on_goal -1 =>
      (rintro result ν ⟨hresult, hheader, hkeys, hkeepKeys⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (dst + LightRadixKeys.offset xs.length J : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hresult, LightRadixKeys.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hresult, LightRadixKeys.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hresult, LightRadixKeys.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨rfl, hheader, hkeys, ?_⟩
  intro a ha
  exact (hkeepKeys a (by omega)).trans (hkeepTable a (Or.inl ha))
end ThreeSum.LightFixedRadixDictionary
