-- Prove2me | solution 1 for ThreeSum.LightLocalCoverCandidate.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:57:59.432418+00:00
-- url     : https://prove2.me/submissions/d99e86b7-0718-4f60-bb2c-617c01546688

import Definitions.Def_Submission_ThreeSum_LightWeightDecode
import Definitions.Def_Submission_ThreeSum_LightLocalCoverHashHistogram
import Definitions.Def_Submission_ThreeSum_LightLocalCoverRow
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCandidate
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightHashHistogram_Procs_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_le
import Definitions.Def_WeightedCache3SUM_Alias_da105011ac4dcdd4
import Definitions.Def_WeightedCache3SUM_Alias_a64b3be7ea8b7b19
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Definitions.Def_WeightedCache3SUM_Alias_9176929b72776235
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Theorems.Thm_ThreeSum_LightResidues_residue_lt
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_66dd70707634c020
import Definitions.Def_WeightedCache3SUM_Alias_cdc5e7727f35fd80
import Definitions.Def_WeightedCache3SUM_Alias_de9d37b5900d1a92
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599
import Theorems.Thm_ThreeSum_WeightEnumeration_digit_lt
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverCandidate
open Light
set_option maxHeartbeats 2000000
set_option maxRecDepth 6000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightLocalCoverCandidate
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ}
    {L n p cap index masks bitPtr coef raw0 raw1 hist0 hist1 dst work : ℕ} (mask w0 w1 : ℕ → ℕ) (bits : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + L + 4 ≤ lim.depth) (hp : 0 < p) (hn : 0 < n)
    (hspace : space work L n p ≤ lim.space) (hmasks : masks + n ≤ coef) (hbits : bitPtr + n * L ≤ coef)
    (hcoef : coef + 2 * L ≤ raw0) (hraw0 : raw0 + 2 * n ≤ raw1) (hraw1 : raw1 + 2 * n ≤ hist0)
    (hhist0 : hist0 + p ≤ hist1) (hhist1 : hist1 + p ≤ dst) (hdst : dst + p * p ≤ work)
    (hword : (word L n p cap index : ℤ) ≤ lim.word) (hmaskRead : ∀ i < n, μ (masks + i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2 ^ L) (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr + i * L + j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hw0 : ∀ i < L, w0 i = WeightEnumeration.digit p (2 * L) index (2 * i))
    (hw1 : ∀ i < L, w1 i = WeightEnumeration.digit p (2 * L) index (2 * i + 1)) :
    Meets lim P pMain d [L, p, index, n, cap, masks, bitPtr, coef, raw0, raw1, hist0, hist1, dst, work] μ
      (time L n p index)
      (fun _ μ' =>
        LightWeightDecode.Rows μ' coef L p index ∧
          (∀ r < p,
              μ' (hist0 + r) = (LightHistogram.count (LightHashHistogram.code L p mask w0 w1) r n : ℤ) ∧
                μ' (hist1 + r) = (LightHistogram.count (LightHashHistogram.code L p mask w1 w0) r n : ℤ)) ∧
            (∀ r < p * p, μ' (dst + r) = (entry L n p cap mask bits w0 w1 r : ℤ)) ∧
              Preserved μ μ' work coef raw0 raw1 hist0 hist1 dst L n p) :=
  by
  have hwork : work ≤ lim.space := by unfold space at hspace; omega
  have hdecodeSpace : work + (2 * L + 1) ≤ lim.space := by unfold space at hspace; omega
  have hhashSpace : LightHashHistogram.space work L p ≤ lim.space :=
    by
    unfold space at hspace
    unfold LightHashHistogram.space
    omega
  have hrowSpace : work + 2 * (n * n) ≤ lim.space := by unfold space at hspace; omega
  have hbudget (x : ℕ) (hx : x ≤ word L n p cap index) : (x : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hx).trans hword
  have hdecodeWord := hbudget (LightWeightDecode.word L p index) (by unfold word; omega)
  have hhashWord := hbudget (LightHashHistogram.word L p p) (by unfold word; omega)
  have hrowWord := hbudget (LightPairFlags.word L n p cap) (by unfold word; omega)
  have hindexWord := hbudget index (by unfold word LightWeightDecode.word LightWeightRow.word; omega)
  have hnWord := hbudget n (by unfold word LightPairFlags.word; omega)
  have hLWord := hbudget L (by unfold word LightPairFlags.word; omega)
  have hpWord := hbudget p (by unfold word LightPairFlags.word; omega)
  have hcapWord := hbudget cap (by unfold word LightPairFlags.word; omega)
  have hb0 : ∀ i < L, w0 i ≤ p := by
    intro i hi
    rw [hw0 i hi]
    exact Nat.le_of_lt (WeightEnumeration.digit_lt hp)
  have hb1 : ∀ i < L, w1 i ≤ p := by
    intro i hi
    rw [hw1 i hi]
    exact Nat.le_of_lt (WeightEnumeration.digit_lt hp)
  apply Meets.of_body S.main
  unfold body time
  have hdcall :=
    S.decode.meets (d := d + 1) (μ := μ) (L := L) (p := p) (k := index) (dst := coef) (work := work) hw (by omega)
      (by omega) (by omega) hdecodeSpace hdecodeWord
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
    | refine _root_.Light.Ends.callToThen (hdcall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hdcall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWeightDecode.time, LightWeightRow.time,
            LightRadixDigit.time, LightHashHistogram.time, LightLocalCoverRow.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWeightDecode.time, LightWeightRow.time, LightRadixDigit.time, LightHashHistogram.time,
              LightLocalCoverRow.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightDecode.time, LightWeightRow.time,
            LightRadixDigit.time, LightHashHistogram.time, LightLocalCoverRow.time] <;> omega)
    on_goal -1 => (rintro value₀ μ₁ ⟨hrows, _, hkeep₀⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hmask₁ : ∀ i < n, μ₁ (masks + i) = (mask i : ℤ) :=
    by
    intro i hi
    rw [hkeep₀ _ ⟨by omega, Or.inl (by omega)⟩]
    exact hmaskRead i hi
  have hc0 : ∀ i < L, μ₁ (coef + i) = (w0 i : ℤ) := by
    intro i hi
    rw [(hrows i hi).1, hw0 i hi]
  have hc1 : ∀ i < L, μ₁ (coef + L + i) = (w1 i : ℤ) :=
    by
    intro i hi
    rw [(hrows i hi).2, hw1 i hi]
  have hlcall :=
    LightLocalCoverHashHistogram.meets S.hash (d := d + 1) (μ := μ₁) (L := L) (n := n) (p := p) (U := p) (masks :=
      masks) (raw := raw0) (codes := raw0 + n) (hist := hist0) (src0 := coef) (src1 := coef + L) (work := work) mask w0
      w1 hw (by omega) hp hhashSpace (by omega) (by omega) (by omega) le_rfl (by omega) (by omega) hhashWord hmask₁
      hmaskLt hc0 hc1 hb0 hb1
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
    | refine _root_.Light.Ends.callToThen (hlcall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hlcall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWeightDecode.time, LightWeightRow.time,
            LightRadixDigit.time, LightHashHistogram.time, LightLocalCoverRow.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWeightDecode.time, LightWeightRow.time, LightRadixDigit.time, LightHashHistogram.time,
              LightLocalCoverRow.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightDecode.time, LightWeightRow.time,
            LightRadixDigit.time, LightHashHistogram.time, LightLocalCoverRow.time] <;> omega)
    on_goal -1 =>
      (rintro value₁ μ₂ ⟨hleftCodes, hleftCounts, hkeep₁, hpres₁⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hmask₂ : ∀ i < n, μ₂ (masks + i) = (mask i : ℤ) :=
    by
    intro i hi
    rw [hkeep₁ _ (by omega)]
    exact hmask₁ i hi
  have hc0₂ : ∀ i < L, μ₂ (coef + i) = (w0 i : ℤ) := by
    intro i hi
    rw [hkeep₁ _ (by omega)]
    exact hc0 i hi
  have hc1₂ : ∀ i < L, μ₂ (coef + L + i) = (w1 i : ℤ) :=
    by
    intro i hi
    rw [hkeep₁ _ (by omega)]
    exact hc1 i hi
  have hrcall :=
    LightLocalCoverHashHistogram.meets S.hash (d := d + 1) (μ := μ₂) (L := L) (n := n) (p := p) (U := p) (masks :=
      masks) (raw := raw1) (codes := raw1 + n) (hist := hist1) (src0 := coef + L) (src1 := coef) (work := work) mask w1
      w0 hw (by omega) hp hhashSpace (by omega) (by omega) (by omega) le_rfl (by omega) (by omega) hhashWord hmask₂
      hmaskLt hc1₂ hc0₂ hb1 hb0
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
    | refine _root_.Light.Ends.callToThen (hrcall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hrcall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWeightDecode.time, LightWeightRow.time,
            LightRadixDigit.time, LightHashHistogram.time, LightLocalCoverRow.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWeightDecode.time, LightWeightRow.time, LightRadixDigit.time, LightHashHistogram.time,
              LightLocalCoverRow.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightDecode.time, LightWeightRow.time,
            LightRadixDigit.time, LightHashHistogram.time, LightLocalCoverRow.time] <;> omega)
    on_goal -1 =>
      (rintro value₂ μ₃ ⟨hrightCodes, hrightCounts, hkeep₂, hpres₂⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hleftCodes₃ : ∀ i < n, μ₃ (raw0 + n + i) = (LightHashHistogram.code L p mask w0 w1 i : ℤ) :=
    by
    intro i hi
    rw [hkeep₂ _ (by omega)]
    exact hleftCodes i hi
  have hleftCounts₃ :
    ∀ r < p, μ₃ (hist0 + r) = (LightHistogram.count (LightHashHistogram.code L p mask w0 w1) r n : ℤ) :=
    by
    intro r hr
    rw [hpres₂ _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))]
    exact hleftCounts r hr
  have hbits₃ : ∀ i < n, ∀ j < L, μ₃ (bitPtr + i * L + j) = (bits i j : ℤ) :=
    by
    intro i hi j hj
    have hm := Nat.mul_le_mul_right L (show i + 1 ≤ n by omega)
    have ha : bitPtr + i * L + j < coef := by nlinarith
    rw [hkeep₂ _ (by omega), hkeep₁ _ (by omega), hkeep₀ _ ⟨by omega, Or.inl ha⟩]
    exact hbitsRead i hi j hj
  have hrowcall :=
    S.row.meets (d := d + 1) (μ := μ₃) (bitPtr := bitPtr) (leftPtr := raw0 + n) (rightPtr := raw1 + n) (leftHist :=
      hist0) (rightHist := hist1) (dst := dst) (n := n) (L := L) (p := p) (cap := cap) (keys := work) bits
      (LightHashHistogram.code L p mask w0 w1) (LightHashHistogram.code L p mask w1 w0)
      (fun r => LightHistogram.count (LightHashHistogram.code L p mask w0 w1) r n)
      (fun r => LightHistogram.count (LightHashHistogram.code L p mask w1 w0) r n) hw (by omega) hn hp (by omega)
      (by omega) (by omega) (by omega) (by omega) hdst hrowSpace hrowWord hbits₃ hbitsValue hleftCodes₃ hrightCodes
      (fun _ _ => LightResidues.residue_lt hp 1 _) (fun _ _ => LightResidues.residue_lt hp 1 _) hleftCounts₃
      hrightCounts (fun r _ => LightHistogram.count_le _ r n) (fun r _ => LightHistogram.count_le _ r n)
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
    | refine _root_.Light.Ends.callToThen (hrowcall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hrowcall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWeightDecode.time, LightWeightRow.time,
            LightRadixDigit.time, LightHashHistogram.time, LightLocalCoverRow.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWeightDecode.time, LightWeightRow.time, LightRadixDigit.time, LightHashHistogram.time,
              LightLocalCoverRow.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightDecode.time, LightWeightRow.time,
            LightRadixDigit.time, LightHashHistogram.time, LightLocalCoverRow.time] <;> omega)
    on_goal -1 => (rintro value₃ μ₄ ⟨hout, hkeep₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨?_, ?_, hout, ?_⟩
  · intro i hi
    constructor
    · change μ₄ (coef + i) = _
      rw [hkeep₃ _ ⟨by omega, Or.inl (by omega)⟩, hkeep₂ _ (by omega), hkeep₁ _ (by omega)]
      exact (hrows i hi).1
    · change μ₄ (coef + L + i) = _
      rw [hkeep₃ _ ⟨by omega, Or.inl (by omega)⟩, hkeep₂ _ (by omega), hkeep₁ _ (by omega)]
      exact (hrows i hi).2
  · intro r hr
    constructor
    · change μ₄ (hist0 + r) = _
      rw [hkeep₃ _ ⟨by omega, Or.inl (by omega)⟩]
      exact hleftCounts₃ r hr
    · change μ₄ (hist1 + r) = _
      rw [hkeep₃ _ ⟨by omega, Or.inl (by omega)⟩]
      exact hrightCounts r hr
  · intro a ha hc hr0 hr1 hh0 hh1 hd
    change μ₄ a = μ a
    rw [hkeep₃ a ⟨ha, hd⟩, hpres₂ a ha (by omega) (by omega) hh1, hpres₁ a ha (by omega) (by omega) hh0]
    exact hkeep₀ a ⟨ha, hc⟩
end Procs
end ThreeSum.LightLocalCoverCandidate
