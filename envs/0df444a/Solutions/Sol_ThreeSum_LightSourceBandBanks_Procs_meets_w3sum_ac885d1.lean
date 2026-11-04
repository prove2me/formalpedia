-- Prove2me | solution 1 for ThreeSum.LightSourceBandBanks.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:56:27.683791+00:00
-- url     : https://prove2.me/submissions/fce364fa-5e69-4c9f-b781-09aef0db4337

import Definitions.Def_Submission_ThreeSum_LightSourceBandBankBatch
import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Definitions.Def_Submission_ThreeSum_LightSourceOccurrenceArray
import Definitions.Def_Submission_ThreeSum_LightSourceBandBanks
import Definitions.Def_WeightedCache3SUM_Alias_1ce1218b74f93d21
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_ThreeSum_BandPartition_size_le
import Theorems.Thm_ThreeSum_SourceBandBankData_Stored_heads_read
import Theorems.Thm_ThreeSum_SourceBandPairData_ordered
import Theorems.Thm_ThreeSum_SourceBandPairSlices_heads_read
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBandBanks
open Light GlobalEncoding BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds SubsetAddress BlockSourceOccurrenceOrder SourceBandBankLayout SourceBandBankData
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBandBanks
namespace Procs
theorem _root_.solution {pMain : ℕ} (C : Procs P pMain) {μ : ℕ → ℤ} {fL fR : ℕ → ℤ}
    {pair NL NR g p h J cut occ maps candidates histL histR base : ℕ} {shift : ℤ}
    (H : SourceBandPairData.Stored μ fL fR pair NL NR g p (modulus h J) shift) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + J * (512 * h) + 14 ≤ lim.depth) (hg : 0 < g) (hcut : cut ≤ J * (512 * h))
    (hpair : SourceBandPairData.next pair NL NR g (modulus h J) ≤ occ)
    (hocc : occ + LightBlockSourceCatalog.count h J * J ≤ base) (hmaps : maps + 2 * (512 * h) * scheduleSize h ≤ occ)
    (hcandidates : candidates + scheduleSize h ≤ occ)
    (hleft : histL + LightLocalCoverSchedule.rows h * localPrime h ≤ occ)
    (hright : histR + LightLocalCoverSchedule.rows h * localPrime h ≤ occ)
    (hspace : space base NL NR g h J cut ≤ lim.space) (hword : (word NL NR h J : ℤ) ≤ lim.word)
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    Meets lim P pMain d
      [J, 512 * h, h, localPrime h, localBucketCap h, cut, modulus h J, occ, maps, candidates, histL, histR, pair, base,
        downsetCap (J * (512 * h)) cut, LightBlockSourceCatalog.count h J, scheduleSize h, span h J cut]
      μ (time NL NR g h J cut)
      (fun r ν =>
        r = (finish base NL NR g h J cut : ℤ) ∧ Stored ν fL fR base NL NR g h J cut occ (p : ℤ) shift ∧ Kept μ ν occ) :=
  by
  obtain ⟨_, hcountL, _, hcountR, _⟩ := SourceBandPairSlices.heads_read H
  have hsRows :
    LightOutputDecodeDigits.space (finish base NL NR g h J cut) (LightBlockSourceCatalog.count h J) ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hs : finish base NL NR g h J cut ≤ lim.space := by unfold LightOutputDecodeDigits.space at hsRows; omega
  have hfirst : first base ≤ finish base NL NR g h J cut := Nat.le_add_right _ _
  have hbaseSpace : base + 5 ≤ lim.space := hfirst.trans hs
  have ho := SourceBandPairData.ordered pair NL NR g (modulus h J)
  have hhead : pair + 8 ≤ base := by unfold SourceBandPairData.leftBase at ho; omega
  have hwBanks : (LightSourceBandBankStep.word NL NR h J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hNL := BandPartition.size_le NL g
  have hNR := BandPartition.size_le NR g
  have hcountWordL : (BandPartition.size NL g : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr
          (show BandPartition.size NL g ≤ LightSourceBandBankStep.word NL NR h J by
            unfold LightSourceBandBankStep.word
            omega)).trans
      hwBanks
  have hcountWordR : (BandPartition.size NR g : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr
          (show BandPartition.size NR g ≤ LightSourceBandBankStep.word NL NR h J by
            unfold LightSourceBandBankStep.word
            omega)).trans
      hwBanks
  have h32 : (32 : ℤ) ≤ lim.word := by unfold LightSourceBandBankStep.word at hwBanks; omega
  have haddr1 : ((pair : ℤ) + 1).toNat = pair + 1 := by omega
  have haddr3 : ((pair : ℤ) + 3).toNat = pair + 3 := by omega
  have htime :
    afterTime NL NR g h J cut =
      LightSourceOccurrenceArray.time (LightBlockSourceCatalog.count h J) J +
          LightSourceBandBankBatch.time NL NR g h J cut +
        1000 :=
    rfl
  apply Meets.of_body C.main
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
    refine _root_.Light.Ends.setToThen (BandPartition.size NL g : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcountL, haddr1]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hcountL, haddr1] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcountL, haddr1] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine
      _root_.Light.Ends.iteIffThen ((BandPartition.size NL g : ℤ) < (BandPartition.size NR g : ℤ)) (fun hy => ?_)
        (fun hn => ?_) ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcountR, haddr3]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hcountR, haddr3] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcountR, haddr3] <;> omega)
    all_goals
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
  · have hK : BandPartition.size NR g = SourceBandPairSlices.count NL NR g :=
      by
      unfold SourceBandPairSlices.count
      omega
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (BandPartition.size NR g : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcountR, haddr3]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hcountR, haddr3] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcountR, haddr3] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    focus
      (refine
          _root_.Light.Ends.pieceLast
            (afterCount_ends C.rows C.digits C.divide C.banks H hw hd hg hcut hK hpair hocc hmaps hcandidates hleft
              hright hspace hword hcover)
            (fun _ h_p2m_6189669801689130842 => h_p2m_6189669801689130842) ?_;
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [] <;> first
                | omega
                | (ring_nf; omega)))
  · have hK : BandPartition.size NL g = SourceBandPairSlices.count NL NR g :=
      by
      unfold SourceBandPairSlices.count
      omega
    focus
      (refine
          _root_.Light.Ends.pieceLast
            (afterCount_ends C.rows C.digits C.divide C.banks H hw hd hg hcut hK hpair hocc hmaps hcandidates hleft
              hright hspace hword hcover)
            (fun _ h_p2m_16725601771917004508 => h_p2m_16725601771917004508) ?_;
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [] <;> first
                | omega
                | (ring_nf; omega)))
end Procs
end ThreeSum.LightSourceBandBanks
