-- Prove2me | solution 1 for ThreeSum.LightWeightDecode.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:43:55.111643+00:00
-- url     : https://prove2.me/submissions/bb288ca9-daa2-4890-9e44-32b8ba993443

import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightWeightDecode
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_powTable_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightDecode
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightWeightDecode
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ} {L p k dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 2 < lim.depth) (hp : 1 ≤ p) (hdst : dst + 2 * L ≤ work)
    (hspace : work + (2 * L + 1) ≤ lim.space) (hword : (word L p k : ℤ) ≤ lim.word) :
    Meets lim P pMain d [L, p, k, dst, work] μ (time L k)
      (fun _ μ' =>
        Rows μ' dst L p k ∧ (∀ e ≤ 2 * L, μ' (work + e) = ((p ^ e : ℕ) : ℤ)) ∧ KeptBut μ μ' work dst (2 * L)) :=
  by
  have hbudget (x : ℕ) (hx : x ≤ word L p k) : (x : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hx).trans hword
  have hpWord := hbudget p (by unfold word LightWeightRow.word; omega)
  have hkWord := hbudget k (by unfold word LightWeightRow.word; omega)
  have hWWord := hbudget (2 * L) (by unfold word LightWeightRow.word; omega)
  have hWWordZ : (2 : ℤ) * L ≤ lim.word := by exact_mod_cast hWWord
  have h2Word := hbudget 2 (by unfold word LightWeightRow.word; omega)
  have hpows : ∀ e ≤ 2 * L + 1, ((p ^ e : ℕ) : ℤ) ≤ lim.word :=
    by
    intro e he
    have hh := Nat.pow_le_pow_right hp he
    apply hbudget
    unfold word LightWeightRow.word
    omega
  apply Meets.of_body S.main
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
    refine _root_.Light.Ends.setToThen (2 * L : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWeightRow.time, LightRadixDigit.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWeightRow.time, LightRadixDigit.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightRow.time, LightRadixDigit.time] <;>
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
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((powTable_meets (d := d + 1) (μ := μ) (dst := work) (L := 2 * L + 1) (b := p) S.powers hw hspace hpows) _
            (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (powTable_meets (d := d + 1) (μ := μ) (dst := work) (L := 2 * L + 1) (b := p) S.powers hw hspace hpows) ?_ ?_
          ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWeightRow.time, LightRadixDigit.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWeightRow.time, LightRadixDigit.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightRow.time, LightRadixDigit.time] <;>
          omega)
    on_goal -1 => (rintro value₀ μ₁ ⟨hpow, hkeep₀⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hpow₁ : ∀ e ≤ 2 * L, μ₁ (work + e) = ((p ^ e : ℕ) : ℤ) :=
    by
    intro e he
    exact (hpow e (by simp; omega)).trans (getElem_powList _)
  have hword₀ : (LightWeightRow.word (2 * L) p k 0 2 : ℤ) ≤ lim.word :=
    by
    have hh : LightWeightRow.word (2 * L) p k 0 2 ≤ word L p k :=
      by
      unfold word LightWeightRow.word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hrow₀ :=
    LightWeightRow.meets (d := d + 1) (μ := μ₁) (W := 2 * L) (p := p) (k := k) (powers := work) (start := 0) (stride :=
      2) (dst := dst) (n := L) S.row S.digit S.divide hw (by omega) hp (by omega) hspace (Or.inr (by omega)) hword₀
      (by intro i hi; omega) hpow₁
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
    | refine _root_.Light.Ends.callToThen (hrow₀ _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hrow₀ ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWeightRow.time, LightRadixDigit.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWeightRow.time, LightRadixDigit.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightRow.time, LightRadixDigit.time] <;>
          omega)
    on_goal -1 => (rintro value₁ μ₂ ⟨hrowValues₀, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hpow₂ : ∀ e ≤ 2 * L, μ₂ (work + e) = ((p ^ e : ℕ) : ℤ) :=
    by
    intro e he
    rw [hkeep₁ _ (Or.inr (by omega))]
    exact hpow₁ e he
  have hrow₁ :=
    LightWeightRow.meets (d := d + 1) (μ := μ₂) (W := 2 * L) (p := p) (k := k) (powers := work) (start := 1) (stride :=
      2) (dst := dst + L) (n := L) S.row S.digit S.divide hw (by omega) hp (by omega) hspace (Or.inr (by omega)) hword
      (by intro i hi; omega) hpow₂
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
    | refine _root_.Light.Ends.callToThen (hrow₁ _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hrow₁ ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWeightRow.time, LightRadixDigit.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWeightRow.time, LightRadixDigit.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightRow.time, LightRadixDigit.time] <;>
          omega)
    on_goal -1 => (rintro value₂ μ₃ ⟨hrowValues₁, hkeep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  change Rows μ₃ dst L p k ∧ (∀ e ≤ 2 * L, μ₃ (work + e) = ((p ^ e : ℕ) : ℤ)) ∧ KeptBut μ μ₃ work dst (2 * L)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    constructor
    · rw [hkeep₂ _ (Or.inl (by omega))]
      simpa only [Nat.zero_add] using hrowValues₀ i hi
    · simpa only [Nat.add_comm 1] using hrowValues₁ i hi
  · intro e he
    rw [hkeep₂ _ (Or.inr (by omega))]
    exact hpow₂ e he
  · intro a ⟨ha, hout⟩
    rw [hkeep₂ _ (by omega), hkeep₁ _ (by omega)]
    exact hkeep₀ a (Or.inl ha)
end Procs
end ThreeSum.LightWeightDecode
