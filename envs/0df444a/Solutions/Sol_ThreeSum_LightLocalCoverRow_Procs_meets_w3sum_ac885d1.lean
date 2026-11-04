-- Prove2me | solution 1 for ThreeSum.LightLocalCoverRow.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:11:37.644657+00:00
-- url     : https://prove2.me/submissions/06c5bdea-9379-46a7-ac12-19fa8ea9fba9

import Definitions.Def_Submission_ThreeSum_LightPairFlags
import Definitions.Def_Submission_ThreeSum_LightSupportMark
import Definitions.Def_Submission_ThreeSum_LightLocalCoverRow
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_9176929b72776235
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_66dd70707634c020
import Definitions.Def_WeightedCache3SUM_Alias_cdc5e7727f35fd80
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverRow
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightLocalCoverRow
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ}
    {bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap keys : ℕ} (bits : ℕ → ℕ → ℕ)
    (left right leftCount rightCount : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) (hn : 0 < n)
    (hp : 0 < p) (hbits : bitPtr + n * L ≤ keys) (hleft : leftPtr + n ≤ keys) (hright : rightPtr + n ≤ keys)
    (hleftHist : leftHist + p ≤ keys) (hrightHist : rightHist + p ≤ keys) (hdst : dst + p * p ≤ keys)
    (hspace : keys + 2 * (n * n) ≤ lim.space) (hword : (LightPairFlags.word L n p cap : ℤ) ≤ lim.word)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr + i * L + j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1) (hleftRead : ∀ i < n, μ (leftPtr + i) = (left i : ℤ))
    (hrightRead : ∀ i < n, μ (rightPtr + i) = (right i : ℤ)) (hleftLt : ∀ i < n, left i < p)
    (hrightLt : ∀ i < n, right i < p) (hleftCount : ∀ r < p, μ (leftHist + r) = (leftCount r : ℤ))
    (hrightCount : ∀ r < p, μ (rightHist + r) = (rightCount r : ℤ)) (hleftBound : ∀ r < p, leftCount r ≤ n)
    (hrightBound : ∀ r < p, rightCount r ≤ n) :
    Meets lim P pMain d [bitPtr, leftPtr, rightPtr, leftHist, rightHist, dst, n, L, p, cap, keys] μ (time L n p)
      (fun _ μ' =>
        (∀ r < p * p,
            μ' (dst + r) =
              (LightSupportMark.bit (LightPairFlags.pairKey n p left right)
                  (LightPairFlags.pairFlag L n cap bits left right leftCount rightCount) r (n * n) :
                ℤ)) ∧
          KeptBut μ μ' keys dst (p * p)) :=
  by
  have hbudget (x : ℕ) (hx : x ≤ LightPairFlags.word L n p cap) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hnWord := hbudget n (by unfold LightPairFlags.word; omega)
  have hpWord := hbudget p (by unfold LightPairFlags.word; omega)
  have hLWord := hbudget L (by unfold LightPairFlags.word; omega)
  have hcapWord := hbudget cap (by unfold LightPairFlags.word; omega)
  have heWord := hbudget (n * n) (by unfold LightPairFlags.word; omega)
  have htWord := hbudget (p * p) (by unfold LightPairFlags.word; omega)
  have h1Word := hbudget 1 (by unfold LightPairFlags.word; omega)
  have heWordZ : (n : ℤ) * n ≤ lim.word := by exact_mod_cast heWord
  have htWordZ : (p : ℤ) * p ≤ lim.word := by exact_mod_cast htWord
  apply Meets.of_body S.main
  unfold body time
  have hpair :=
    LightPairFlags.meets (d := d + 1) (μ := μ) (bitPtr := bitPtr) (leftPtr := leftPtr) (rightPtr := rightPtr)
      (leftHist := leftHist) (rightHist := rightHist) (dst := keys) (n := n) (L := L) (p := p) (cap := cap) S.pair
      S.divide S.dot S.trim bits left right leftCount rightCount hw (by omega) hn hp hbits hleft hright hleftHist
      hrightHist hspace hword hbitsRead hbitsValue hleftRead hrightRead hleftLt hrightLt hleftCount hrightCount
      hleftBound hrightBound
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
    | refine _root_.Light.Ends.callToThen (hpair _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hpair ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightPairFlags.time,
            LightPairFlags.roundTime, LightBooleanDot.time, LightTrimTest.time, LightSupportMark.time,
            LightSupportMark.markTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightPairFlags.time, LightPairFlags.roundTime, LightBooleanDot.time, LightTrimTest.time,
              LightSupportMark.time, LightSupportMark.markTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightPairFlags.time, LightPairFlags.roundTime,
            LightBooleanDot.time, LightTrimTest.time, LightSupportMark.time, LightSupportMark.markTime] <;>
          omega)
    on_goal -1 => (rintro value₀ μ₁ ⟨hkeys, hflags, hkept₀⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hkeyLt : ∀ i < n * n, LightPairFlags.pairKey n p left right i < p * p :=
    by
    intro i hi
    have hq : i / n < n := (Nat.div_lt_iff_lt_mul hn).mpr hi
    have hr := Nat.mod_lt i hn
    have hl := hleftLt _ hq
    have hh := hrightLt _ hr
    unfold LightPairFlags.pairKey
    nlinarith
  have hs :=
    LightSupportMark.meets (d := d + 1) (μ := μ₁) (keys := keys) (flags := keys + n * n) (dst := dst) (n := n * n) (p :=
      p * p) S.support S.fill (LightPairFlags.pairKey n p left right)
      (LightPairFlags.pairFlag L n cap bits left right leftCount rightCount) hw (by omega) (by omega) (by omega)
      (by omega) (Or.inr hdst) (Or.inr (by omega)) hkeys hflags hkeyLt h1Word
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
    | refine _root_.Light.Ends.callToThen (hs _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hs ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightPairFlags.time,
            LightPairFlags.roundTime, LightBooleanDot.time, LightTrimTest.time, LightSupportMark.time,
            LightSupportMark.markTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightPairFlags.time, LightPairFlags.roundTime, LightBooleanDot.time, LightTrimTest.time,
              LightSupportMark.time, LightSupportMark.markTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightPairFlags.time, LightPairFlags.roundTime,
            LightBooleanDot.time, LightTrimTest.time, LightSupportMark.time, LightSupportMark.markTime] <;>
          omega)
    on_goal -1 => (rintro value₁ μ₂ ⟨hrow, hkept₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨hrow, ?_⟩
  intro a ⟨ha, hout⟩
  change μ₂ a = μ a
  rw [hkept₁ a hout]
  exact hkept₀ a (Or.inl ha)
end Procs
end ThreeSum.LightLocalCoverRow
