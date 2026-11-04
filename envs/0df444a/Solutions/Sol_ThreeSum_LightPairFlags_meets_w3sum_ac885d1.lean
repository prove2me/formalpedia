-- Prove2me | solution 1 for ThreeSum.LightPairFlags.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:54:04.519063+00:00
-- url     : https://prove2.me/submissions/226c0ded-aa64-4f03-92fe-3250858ce2e9

import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightTrimTest
import Definitions.Def_Submission_ThreeSum_LightPairFlags
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightTrimTest_flag_le
import Definitions.Def_WeightedCache3SUM_Alias_cdc5e7727f35fd80
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightPairFlags
open Light
set_option maxHeartbeats 1500000
set_option maxRecDepth 5000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightPairFlags
theorem _root_.solution {pMain pDivide pDot pTrim : ℕ} (hmain : P[pMain]? = some (body pDivide pDot pTrim))
    (hdivide : P[pDivide]? = some LightSmallDivide.body) (hdot : P[pDot]? = some LightBooleanDot.body)
    (htrim : P[pTrim]? = some LightTrimTest.body) {μ : ℕ → ℤ}
    {bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap : ℕ} (bits : ℕ → ℕ → ℕ)
    (left right leftCount rightCount : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hn : 0 < n)
    (hp : 0 < p) (hbits : bitPtr + n * L ≤ dst) (hleft : leftPtr + n ≤ dst) (hright : rightPtr + n ≤ dst)
    (hleftHist : leftHist + p ≤ dst) (hrightHist : rightHist + p ≤ dst) (hspace : dst + 2 * (n * n) ≤ lim.space)
    (hword : (word L n p cap : ℤ) ≤ lim.word) (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr + i * L + j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1) (hleftRead : ∀ i < n, μ (leftPtr + i) = (left i : ℤ))
    (hrightRead : ∀ i < n, μ (rightPtr + i) = (right i : ℤ)) (hleftLt : ∀ i < n, left i < p)
    (hrightLt : ∀ i < n, right i < p) (hleftCount : ∀ r < p, μ (leftHist + r) = (leftCount r : ℤ))
    (hrightCount : ∀ r < p, μ (rightHist + r) = (rightCount r : ℤ)) (hleftBound : ∀ r < p, leftCount r ≤ n)
    (hrightBound : ∀ r < p, rightCount r ≤ n) :
    Meets lim P pMain d [bitPtr, leftPtr, rightPtr, leftHist, rightHist, dst, n, L, p, cap] μ (time L n)
      (fun _ μ' =>
        (∀ i < n * n, μ' (dst + i) = (pairKey n p left right i : ℤ)) ∧
          (∀ i < n * n, μ' (dst + n * n + i) = (pairFlag L n cap bits left right leftCount rightCount i : ℤ)) ∧
            SameOutside μ μ' dst (2 * (n * n))) :=
  by
  have hbudget (x : ℕ) (hx : x ≤ word L n p cap) : (x : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hx).trans hword
  have hnWord := hbudget n (by unfold word; omega)
  have hpWord := hbudget p (by unfold word; omega)
  have hcapWord := hbudget cap (by unfold word; omega)
  have hLWord := hbudget L (by unfold word; omega)
  have heWord := hbudget (n * n) (by unfold word; omega)
  have h1Word := hbudget 1 (by unfold word; omega)
  have heWordZ : (n : ℤ) * (n : ℤ) ≤ lim.word := by exact_mod_cast heWord
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
    refine _root_.Light.Ends.setToThen (dst + n * n : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, roundTime, word]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [roundTime, word] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, roundTime, word] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.for (Inv μ bits left right leftCount rightCount bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap)
      (n * n) (roundTime L n) ?_ ?_ ?_ ?_ (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, roundTime, LightBooleanDot.time,
            LightTrimTest.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [roundTime, LightBooleanDot.time, LightTrimTest.time] <;>
            first
            | omega
            | (ring_nf; omega)))
  · refine ⟨0, 0, 0, 0, 0, 0, μ, ?_, ?_, ?_, SameOutside.refl⟩
    · exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 6).symm)
    · intro j hj; omega
    · intro j hj; omega
  · rintro i _ hi _ ⟨a, b, c, e, f, g, μ', rfl, writtenKeys, writtenFlags, kept⟩
    have hq : i / n < n := (Nat.div_lt_iff_lt_mul hn).mpr hi
    have hr : i % n < n := Nat.mod_lt i hn
    have hqmul : i / n * n ≤ i := Nat.div_mul_le_self i n
    have hqr : i % n + i / n * n = i := by simpa only [Nat.mul_comm] using Nat.mod_add_div i n
    have hdivWord : ((i + n + 2 : ℕ) : ℤ) ≤ lim.word := hbudget _ (by unfold word; omega)
    have hdivTime : LightSmallDivide.time i n ≤ 20 * n + 40 := by unfold LightSmallDivide.time; omega
    have hqWord := hbudget (i / n) (by unfold word; omega)
    have hrWord := hbudget (i % n) (by unfold word; omega)
    have hqNonneg : (0 : ℤ) ≤ (i : ℤ) / (n : ℤ) :=
      by
      rw [← Int.natCast_ediv]
      exact Int.natCast_nonneg _
    have hrem : (i : ℤ) - ((i / n : ℕ) : ℤ) * n = ((i % n : ℕ) : ℤ) := by
      exact_mod_cast (by omega : i - i / n * n = i % n)
    have hqmulZ : ((i / n : ℕ) : ℤ) * (n : ℤ) ≤ lim.word :=
      by
      have hh : i / n * n ≤ word L n p cap := by unfold word; omega
      exact (by exact_mod_cast hh : ((i / n : ℕ) : ℤ) * (n : ℤ) ≤ (word L n p cap : ℤ)).trans hword
    have hqmulInt : (i : ℤ) / (n : ℤ) * n ≤ lim.word := by simpa only [Int.natCast_ediv] using hqmulZ
    have hqmulNonneg : (0 : ℤ) ≤ (i : ℤ) / (n : ℤ) * n :=
      by
      rw [← Int.natCast_ediv, ← Nat.cast_mul]
      exact Int.natCast_nonneg _
    have hremInt : (i : ℤ) - (i : ℤ) / (n : ℤ) * n = ((i % n : ℕ) : ℤ) := by simpa only [Int.natCast_ediv] using hrem
    unfold roundBody
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
            ((LightSmallDivide.meets (d := d + 1) (a := i) (b := n) hdivide μ' hdivWord) _ (by omega)) ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen (LightSmallDivide.meets (d := d + 1) (a := i) (b := n) hdivide μ' hdivWord) ?_ ?_
            ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, roundTime,
              LightBooleanDot.time, LightTrimTest.time, LightSmallDivide.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [roundTime, LightBooleanDot.time, LightTrimTest.time, LightSmallDivide.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, roundTime, LightBooleanDot.time,
              LightTrimTest.time, LightSmallDivide.time] <;>
            omega)
      on_goal -1 => (rintro qval μ₁ ⟨hqval, hmem₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst μ₁
    subst qval
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (i % n : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hremInt, roundTime,
              LightBooleanDot.time, LightTrimTest.time, LightSmallDivide.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hremInt, roundTime, LightBooleanDot.time, LightTrimTest.time, LightSmallDivide.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hremInt, roundTime, LightBooleanDot.time,
              LightTrimTest.time, LightSmallDivide.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    have hqL : (i / n + 1) * L ≤ n * L := Nat.mul_le_mul_right L (by omega)
    have hrL : (i % n + 1) * L ≤ n * L := Nat.mul_le_mul_right L (by omega)
    have hqRow : bitPtr + i / n * L + L ≤ dst := by nlinarith
    have hrRow : bitPtr + i % n * L + L ≤ dst := by nlinarith
    have hqRead : ∀ j < L, μ' (bitPtr + i / n * L + j) = (bits (i / n) j : ℤ) :=
      by
      intro j hj
      rw [kept _ (Or.inl (by omega))]
      exact hbitsRead _ hq j hj
    have hrRead : ∀ j < L, μ' (bitPtr + i % n * L + j) = (bits (i % n) j : ℤ) :=
      by
      intro j hj
      rw [kept _ (Or.inl (by omega))]
      exact hbitsRead _ hr j hj
    have hqLMulWord : (((i / n) * L : ℕ) : ℤ) ≤ lim.word :=
      by
      have hh : (i / n) * L ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have hrLMulWord : (((i % n) * L : ℕ) : ℤ) ≤ lim.word :=
      by
      have hh : (i % n) * L ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have hqLInt : (i : ℤ) / (n : ℤ) * L ≤ lim.word := by simpa only [Nat.cast_mul, Int.natCast_ediv] using hqLMulWord
    have hqLNonneg : (0 : ℤ) ≤ (i : ℤ) / (n : ℤ) * L :=
      by
      rw [← Int.natCast_ediv, ← Nat.cast_mul]
      exact Int.natCast_nonneg _
    have hrLInt : (i : ℤ) % (n : ℤ) * L ≤ lim.word := by simpa only [Nat.cast_mul, Int.natCast_emod] using hrLMulWord
    have hrLNonneg : (0 : ℤ) ≤ (i : ℤ) % (n : ℤ) * L :=
      by
      rw [← Int.natCast_emod, ← Nat.cast_mul]
      exact Int.natCast_nonneg _
    have hqa : ((bitPtr : ℤ) + ((i / n : ℕ) : ℤ) * L).toNat = bitPtr + i / n * L := by
      rw [← Nat.cast_mul, ← Nat.cast_add, Int.toNat_natCast]
    have hra : ((bitPtr : ℤ) + ((i % n : ℕ) : ℤ) * L).toNat = bitPtr + i % n * L := by
      rw [← Nat.cast_mul, ← Nat.cast_add, Int.toNat_natCast]
    have hqaInt : ((bitPtr : ℤ) + (i : ℤ) / (n : ℤ) * L).toNat = bitPtr + i / n * L := by
      simpa only [Int.natCast_ediv] using hqa
    have hraInt : ((bitPtr : ℤ) + (i : ℤ) % (n : ℤ) * L).toNat = bitPtr + i % n * L := by
      simpa only [Int.natCast_emod] using hra
    have hqaBound : (bitPtr : ℤ) + (i : ℤ) / (n : ℤ) * L ≤ lim.word :=
      by
      have hh : ((bitPtr + i / n * L : ℕ) : ℤ) ≤ lim.word := by
        exact (Int.ofNat_le.mpr (by omega : bitPtr + i / n * L ≤ lim.space)).trans hw
      simpa only [Nat.cast_add, Nat.cast_mul, Int.natCast_ediv] using hh
    have hraBound : (bitPtr : ℤ) + (i : ℤ) % (n : ℤ) * L ≤ lim.word :=
      by
      have hh : ((bitPtr + i % n * L : ℕ) : ℤ) ≤ lim.word := by
        exact (Int.ofNat_le.mpr (by omega : bitPtr + i % n * L ≤ lim.space)).trans hw
      simpa only [Nat.cast_add, Nat.cast_mul, Int.natCast_emod] using hh
    have hdotCall :=
      LightBooleanDot.meets (d := d + 1) (μ := μ') (srcA := bitPtr + i / n * L) (srcB := bitPtr + i % n * L) (n := L)
        hdot (bits (i / n)) (bits (i % n)) hw (by omega) (by omega) hqRead hrRead (hbitsValue _ hq) (hbitsValue _ hr)
        h1Word
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
      | refine _root_.Light.Ends.callToThen (hdotCall _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hdotCall ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hqa, hra, hqaInt,
              hraInt, roundTime, LightBooleanDot.time, LightTrimTest.time, LightSmallDivide.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hqa, hra, hqaInt, hraInt, roundTime, LightBooleanDot.time, LightTrimTest.time,
                LightSmallDivide.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hqa, hra, hqaInt, hraInt, roundTime,
              LightBooleanDot.time, LightTrimTest.time, LightSmallDivide.time] <;>
            omega)
      on_goal -1 => (rintro overlap μ₂ ⟨hoverlap, hmem₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst μ₂
    have hlr : μ' (leftPtr + i / n) = (left (i / n) : ℤ) := (kept _ (Or.inl (by omega))).trans (hleftRead _ hq)
    have hrr : μ' (rightPtr + i % n) = (right (i % n) : ℤ) := (kept _ (Or.inl (by omega))).trans (hrightRead _ hr)
    have hlLt := hleftLt _ hq
    have hrLt := hrightLt _ hr
    have hlAddr : ((leftPtr : ℤ) + (i : ℤ) / (n : ℤ)).toNat = leftPtr + i / n := by
      rw [← Int.natCast_ediv, ← Nat.cast_add, Int.toNat_natCast]
    have hrAddr : ((rightPtr : ℤ) + (i : ℤ) % (n : ℤ)).toNat = rightPtr + i % n := by
      rw [← Int.natCast_emod, ← Nat.cast_add, Int.toNat_natCast]
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (left (i / n) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlAddr, hlr,
              roundTime, LightBooleanDot.time, LightTrimTest.time, LightSmallDivide.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hlAddr, hlr, roundTime, LightBooleanDot.time, LightTrimTest.time, LightSmallDivide.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlAddr, hlr, roundTime, LightBooleanDot.time,
              LightTrimTest.time, LightSmallDivide.time] <;>
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
      refine _root_.Light.Ends.setToThen (right (i % n) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrAddr, hrr,
              roundTime, LightBooleanDot.time, LightTrimTest.time, LightSmallDivide.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hrAddr, hrr, roundTime, LightBooleanDot.time, LightTrimTest.time, LightSmallDivide.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrAddr, hrr, roundTime, LightBooleanDot.time,
              LightTrimTest.time, LightSmallDivide.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    have hlc : μ' (leftHist + left (i / n)) = (leftCount (left (i / n)) : ℤ) :=
      (kept _ (Or.inl (by omega))).trans (hleftCount _ hlLt)
    have hrc : μ' (rightHist + right (i % n)) = (rightCount (right (i % n)) : ℤ) :=
      (kept _ (Or.inl (by omega))).trans (hrightCount _ hrLt)
    have hcL := hleftBound _ hlLt
    have hcR := hrightBound _ hrLt
    have ht :=
      LightTrimTest.meets (d := d + 1) (x := LightBooleanDot.dot (bits (i / n)) (bits (i % n)) L) (l :=
        leftCount (left (i / n))) (r := rightCount (right (i % n))) (b := cap) htrim μ' h1Word
        (hbudget _ (by unfold word; omega))
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
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hoverlap, hlc, hrc,
              roundTime, LightBooleanDot.time, LightTrimTest.time, LightSmallDivide.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hoverlap, hlc, hrc, roundTime, LightBooleanDot.time, LightTrimTest.time, LightSmallDivide.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hoverlap, hlc, hrc, roundTime,
              LightBooleanDot.time, LightTrimTest.time, LightSmallDivide.time] <;>
            omega)
      on_goal -1 => (rintro flag μ₃ ⟨hflag, hmem₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst μ₃
    have hk : pairKey n p left right i < p * p := by
      unfold pairKey
      nlinarith
    have hkWord := hbudget (pairKey n p left right i) (by unfold word; omega)
    have hkWordZ : (left (i / n) : ℤ) * p + right (i % n) ≤ lim.word := by
      simpa only [pairKey, Nat.cast_add, Nat.cast_mul] using hkWord
    have hprodWord : ((left (i / n) * p : ℕ) : ℤ) ≤ lim.word :=
      by
      have hh : left (i / n) * p ≤ word L n p cap := by unfold pairKey at hk; unfold word; omega
      exact (Int.ofNat_le.mpr hh).trans hword
    have hflag' : flag = (pairFlag L n cap bits left right leftCount rightCount i : ℤ) := hflag
    have hf : pairFlag L n cap bits left right leftCount rightCount i ≤ 1 := LightTrimTest.flag_le ..
    have hfZ : (pairFlag L n cap bits left right leftCount rightCount i : ℤ) ≤ lim.word := by omega
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + i) (pairKey n p left right i : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, pairKey, roundTime,
              LightBooleanDot.time, LightTrimTest.time, LightSmallDivide.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [pairKey, roundTime, LightBooleanDot.time, LightTrimTest.time, LightSmallDivide.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, pairKey, roundTime, LightBooleanDot.time,
              LightTrimTest.time, LightSmallDivide.time] <;>
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
      refine
        _root_.Light.Ends.storeToThen (dst + n * n + i) (pairFlag L n cap bits left right leftCount rightCount i : ℕ) ?_
          ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hflag', roundTime,
              LightBooleanDot.time, LightTrimTest.time, LightSmallDivide.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hflag', roundTime, LightBooleanDot.time, LightTrimTest.time, LightSmallDivide.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hflag', roundTime, LightBooleanDot.time,
              LightTrimTest.time, LightSmallDivide.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine
      ⟨by simp, (i / n : ℕ), i % n, overlap, left (i / n), right (i % n), flag,
        Function.update (Function.update μ' (dst + i) (pairKey n p left right i : ℤ)) (dst + n * n + i)
          (pairFlag L n cap bits left right leftCount rightCount i : ℤ),
        by simp [update_frame_setLocal], ?_, ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact writtenKeys j hj
      · rw [Function.update_of_ne (by omega), Function.update_self]
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact writtenFlags j hj
      · rw [Function.update_self]
    · exact (kept.update ⟨by omega, by omega⟩ _).update ⟨by omega, by omega⟩ _
  · rintro _ _ ⟨a, b, c, e, f, g, μ', rfl, writtenKeys, writtenFlags, kept⟩
    exact ⟨writtenKeys, writtenFlags, kept⟩
  · rintro i _ _ _ ⟨a, b, c, e, f, g, μ', rfl, _, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightPairFlags
