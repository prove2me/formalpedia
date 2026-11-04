-- Prove2me | solution 1 for ThreeSum.LightWeightedPredecessorTable.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:12:22.313518+00:00
-- url     : https://prove2.me/submissions/d0e239e6-bf87-48eb-872b-a98c2047a254

import Definitions.Def_Submission_Weighted_Predecessor
import Definitions.Def_Submission_Weighted_PredecessorTable
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_keptApart_refl
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_writeRecord_kept
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_keptApart_outside
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_writeRecord_current
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_writeRecord_before
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightTernaryCodes_digit_le_two
import Theorems.Thm_ThreeSum_LightTernaryCodes_digit_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_meets
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedAddresses.codes_length
attribute [local simp] ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedPredecessorTable
theorem _root_.solution
    {pMain pCell pDigit pZero pErase pRank pSearch N low high a n powers bank nb bv near nn nv L T active dst stride d :
      ℕ}
    (hmain : P[pMain]? = some (body pCell pDigit))
    (hcell : P[pCell]? = some (LightWeightedPredecessor.body pDigit pZero pErase pRank pSearch))
    (hdigit : P[pDigit]? = some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]? = some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase)) (hrank : P[pRank]? = some (LightWeightedCost.body pDigit))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch)) (μ : ℕ → ℤ)
    (codes bankCodes nearCodes bi ni : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (ha : a + n ≤ dst)
    (hbankSpace : bank + nb ≤ dst) (hnearSpace : near + nn ≤ dst) (hspace : powers + (2 * N + 1) ≤ dst)
    (hdst : dst + 2 * stride * n ≤ lim.space) (hbankVals : bv + nb ≤ lim.space) (hnearVals : nv + nn ≤ lim.space)
    (hword : ((nb + nn + 2 ^ (2 * N + 1) + 1025 * N + 1100 : ℕ) : ℤ) ≤ lim.word)
    (hcontrols : ((T + active + stride + 16 : ℕ) : ℤ) ≤ lim.word) (hread : ∀ j < n, μ (a + j) = (codes j : ℤ))
    (hbankRead : ∀ j < nb, μ (bank + j) = (bankCodes j : ℤ)) (hnearRead : ∀ j < nn, μ (near + j) = (nearCodes j : ℤ))
    (hbankSorted : ∀ j k, j < k → k < nb → bankCodes j < bankCodes k)
    (hnearSorted : ∀ j k, j < k → k < nn → nearCodes j < nearCodes k) (hpowers : Powers μ powers (2 * N))
    (hcodes : ∀ j < n, codes j < 2 ^ (2 * N)) (hlow : low ≤ 2 * N) (hhigh : high ≤ 2 * N) (hL : L ≤ 2 * N)
    (hnb : nb < 2 ^ L) (hnn : nn < 2 ^ L) (hnbpos : 0 < nb) (hactive : active ≤ 1) (hstride : 0 < stride)
    (hbi :
      ∀ j < n,
        active ≠ 0 →
          digit N low high (codes j) ≠ 0 →
            predCost N low high (codes j) ≤ T → bi j < nb ∧ bankCodes (bi j) = code N low high (codes j))
    (hni :
      ∀ j < n,
        active ≠ 0 →
          digit N low high (codes j) ≠ 0 →
            T < predCost N low high (codes j) → ni j < nn ∧ nearCodes (ni j) = code N low high (codes j))
    (hd : d + 2 * N + 4 ≤ lim.depth) :
    Meets lim P pMain d [N, low, high, a, n, powers, bank, nb, bv, near, nn, nv, L, T, active, dst, stride] μ
      (time N L n)
      (fun _ ν =>
        (∀ j < n, RecordAt ν dst stride n j N low high (codes j) T active bv nv (bi j) (ni j)) ∧
          KeptApart μ ν dst stride n ∧ SameOutside μ ν dst (2 * stride * n)) :=
  by
  have hpowWord : ((2 ^ (2 * N + 1) : ℕ) : ℤ) ≤ lim.word := by omega
  have htwoword : (2 : ℤ) ≤ lim.word := by omega
  have hspan : dst + 2 * (stride * n) ≤ lim.space := by simpa only [Nat.mul_assoc] using hdst
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.for (Inv μ N low high a n powers bank nb bv near nn nv L T active dst stride codes bi ni) n
      (LightWeightedPredecessor.time N L + LightTernaryCodes.digitTime (2 * N) + 180) ?start ?round ?done ?bound (hT :=
      by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, 0, 0, μ, ?_, keptApart_refl μ dst stride n, ?_⟩
    · simp [update_frame_setLocal]
      change
        frame [(N : ℤ), low, high, a, n, powers, bank, nb, bv, near, nn, nv, L, T, active, dst, stride, 0] =
          frame
            ([(N : ℤ), low, high, a, n, powers, bank, nb, bv, near, nn, nv, L, T, active, dst, stride, 0] ++ [0, 0, 0])
      exact (frame_append_zeros _ 3).symm
    · intro l hl
      omega
  case round =>
    rintro j _ hj _ ⟨m, k, q, ν, rfl, H, hr⟩
    have hkeep : ∀ x < dst, ν x = μ x := by
      intro x hx
      exact (keptApart_outside hstride H) x (Or.inl hx)
    have hreadj : ν (a + j) = (codes j : ℤ) := by rw [hkeep _ (by omega), hread j hj]
    have hbRead : ∀ l < nb, ν (bank + l) = (bankCodes l : ℤ) := by intro l hl; rw [hkeep _ (by omega), hbankRead l hl]
    have hnRead : ∀ l < nn, ν (near + l) = (nearCodes l : ℤ) := by intro l hl; rw [hkeep _ (by omega), hnearRead l hl]
    have hp : Powers ν powers (2 * N) := by intro l hl; rw [hkeep _ (by omega), hpowers l hl]
    have hm := hcodes j hj
    have hmword : (codes j : ℤ) < lim.word :=
      by
      have hh : 2 ^ (2 * N) ≤ 2 ^ (2 * N + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      exact (Int.ofNat_lt.mpr hm).trans_le ((Int.ofNat_le.mpr hh).trans hpowWord)
    have hdigitBound := LightTernaryCodes.digit_le_two (2 * N) low high (codes j)
    have hweightEq : active * digit N low high (codes j) = weight N low high (codes j) active :=
      by
      by_cases ha : active = 0
      · simp [weight, ha]
      · have ha1 : active = 1 := by omega
        simp [weight, ha1]
    have hweightBound : weight N low high (codes j) active ≤ 2 :=
      by
      unfold weight digit
      split_ifs <;> omega
    have hweightCast :
      (active : ℤ) * (LightTernaryCodes.digit (2 * N) low high (codes j) : ℤ) =
        (weight N low high (codes j) active : ℤ) :=
      by exact_mod_cast hweightEq
    have hkeySpace : key N low high (codes j) T active bv nv (bi j) (ni j) < lim.space :=
      by
      unfold key
      split_ifs with h0 hb
      · omega
      · have hh := hbi j hj (by tauto) (by tauto) hb
        omega
      · have hh := hni j hj (by tauto) (by tauto) (by omega)
        omega
    have hkeyWord : (key N low high (codes j) T active bv nv (bi j) (ni j) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (Nat.le_of_lt hkeySpace)).trans hw
    have hprod : stride * j < stride * n := Nat.mul_lt_mul_of_pos_left hj hstride
    have hprodWord : ((stride * j : ℕ) : ℤ) ≤ lim.word :=
      by
      have hh : stride * j ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have hprodNWord : ((stride * n : ℕ) : ℤ) ≤ lim.word :=
      by
      have hh : stride * n ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have hc :=
      LightWeightedPredecessor.meets (d := d + 1) hcell hdigit hzero herase hrank hsearch ν bankCodes nearCodes hw
        (by omega) (by omega) hbankVals hnearVals (by omega) hword (by omega) hbRead hnRead hbankSorted hnearSorted hp
        hm hlow hhigh hL hnb hnn hnbpos (hbi j hj) (hni j hj) (by omega)
    have hdc :=
      LightTernaryCodes.digit_meets (d := d + 1) hdigit herase ν hw (by omega) hpowWord hp hlow hhigh hm (by omega)
        htwoword
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
      refine _root_.Light.Ends.setToThen (codes j : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadj,
              LightWeightedPredecessor.time, LightTernaryCodes.digitTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hreadj, LightWeightedPredecessor.time, LightTernaryCodes.digitTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadj, LightWeightedPredecessor.time,
              LightTernaryCodes.digitTime] <;>
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
      | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightWeightedPredecessor.time, LightTernaryCodes.digitTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightWeightedPredecessor.time, LightTernaryCodes.digitTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightedPredecessor.time,
              LightTernaryCodes.digitTime] <;>
            omega)
      on_goal -1 => (rintro out ξ ⟨hout, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ξ
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
      | refine _root_.Light.Ends.callToThen (hdc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hdc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightWeightedPredecessor.time, LightTernaryCodes.digitTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightWeightedPredecessor.time, LightTernaryCodes.digitTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightedPredecessor.time,
              LightTernaryCodes.digitTime] <;>
            omega)
      on_goal -1 => (rintro dig ξ ⟨hdig, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ξ
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (weight N low high (codes j) active : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hdig, hweightCast,
              LightWeightedPredecessor.time, LightTernaryCodes.digitTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hdig, hweightCast, LightWeightedPredecessor.time, LightTernaryCodes.digitTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hdig, hweightCast,
              LightWeightedPredecessor.time, LightTernaryCodes.digitTime] <;>
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
      refine _root_.Light.Ends.storeToThen (dst + stride * j) (weight N low high (codes j) active : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightWeightedPredecessor.time, LightTernaryCodes.digitTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightWeightedPredecessor.time, LightTernaryCodes.digitTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightedPredecessor.time,
              LightTernaryCodes.digitTime] <;>
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
        _root_.Light.Ends.storeToThen (dst + stride * n + stride * j)
          (key N low high (codes j) T active bv nv (bi j) (ni j) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hout,
              LightWeightedPredecessor.time, LightTernaryCodes.digitTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hout, LightWeightedPredecessor.time, LightTernaryCodes.digitTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hout, LightWeightedPredecessor.time,
              LightTernaryCodes.digitTime] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    let ξ :=
      writeRecord ν dst stride n j (weight N low high (codes j) active)
        (key N low high (codes j) T active bv nv (bi j) (ni j))
    refine ⟨by simp, (codes j : ℤ), out, (weight N low high (codes j) active : ℤ), ξ, ?_, ?_, ?_⟩
    · simp [update_frame_setLocal, ξ, writeRecord]
    · intro x hx
      exact (writeRecord_kept hj x hx).trans (H x hx)
    · intro l hl
      rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
      · exact writeRecord_before hstride hl hj (hr l hl)
      · exact writeRecord_current hstride hj
  case done =>
    rintro _ _ ⟨m, k, q, ν, rfl, H, hr⟩
    exact ⟨hr, H, keptApart_outside hstride H⟩
  case bound =>
    rintro j _ hj _ ⟨m, k, q, ν, rfl, H, hr⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightWeightedPredecessorTable
