-- Prove2me | solution 1 for ThreeSum.LightLocalCoverMatrix.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:10:21.364814+00:00
-- url     : https://prove2.me/submissions/e9c0d361-a613-4615-a455-9e0f80638b5e

import Definitions.Def_Submission_ThreeSum_LightLocalCoverCandidate
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMatrix
import Theorems.Thm_Light_Meets_mono_time
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightHashHistogram_Procs_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Definitions.Def_WeightedCache3SUM_Alias_d5eaa25d4585cc6b
import Definitions.Def_WeightedCache3SUM_Alias_da105011ac4dcdd4
import Definitions.Def_WeightedCache3SUM_Alias_a64b3be7ea8b7b19
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Definitions.Def_WeightedCache3SUM_Alias_9176929b72776235
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_66dd70707634c020
import Definitions.Def_WeightedCache3SUM_Alias_cdc5e7727f35fd80
import Definitions.Def_WeightedCache3SUM_Alias_de9d37b5900d1a92
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
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
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverMatrix
open Light
set_option maxHeartbeats 2000000
set_option maxRecDepth 6000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightLocalCoverMatrix
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ}
    {L n p cap N masks bitPtr maps raw0 raw1 hist0 hist1 dst work : ℕ} (mask : ℕ → ℕ) (bits : ℕ → ℕ → ℕ)
    (w0 w1 : ℕ → ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + L + 5 ≤ lim.depth) (hp : 0 < p) (hn : 0 < n)
    (hspace : LightLocalCoverCandidate.space work L n p ≤ lim.space) (hmasks : masks + n ≤ maps)
    (hbits : bitPtr + n * L ≤ maps) (hmaps : maps + N * (2 * L) ≤ raw0) (hraw0 : raw0 + 2 * n ≤ raw1)
    (hraw1 : raw1 + 2 * n ≤ hist0) (hhist0 : hist0 + N * p ≤ hist1) (hhist1 : hist1 + N * p ≤ dst)
    (hdst : dst + N * (p * p) ≤ work) (hword : (LightLocalCoverCandidate.word L n p cap N : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks + i) = (mask i : ℤ)) (hmaskLt : ∀ i < n, mask i < 2 ^ L)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr + i * L + j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hw0 : ∀ j < N, ∀ i < L, w0 j i = WeightEnumeration.digit p (2 * L) j (2 * i))
    (hw1 : ∀ j < N, ∀ i < L, w1 j i = WeightEnumeration.digit p (2 * L) j (2 * i + 1)) :
    Meets lim P pMain d [L, p, N, n, cap, masks, bitPtr, maps, raw0, raw1, hist0, hist1, dst, work] μ (time L n p N)
      (fun _ μ' => Tables μ' L n p cap maps hist0 hist1 dst mask bits w0 w1 N ∧ Kept μ μ' maps) :=
  by
  have hwork : work ≤ lim.space := by unfold LightLocalCoverCandidate.space at hspace; omega
  have hbudget (x : ℕ) (hx : x ≤ LightLocalCoverCandidate.word L n p cap N) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hNWord :=
    hbudget N
      (by
        unfold LightLocalCoverCandidate.word LightWeightDecode.word LightWeightRow.word
        omega)
  have hnWord := hbudget n (by unfold LightLocalCoverCandidate.word LightPairFlags.word; omega)
  have hpWord := hbudget p (by unfold LightLocalCoverCandidate.word LightPairFlags.word; omega)
  have hLWord := hbudget L (by unfold LightLocalCoverCandidate.word LightPairFlags.word; omega)
  have hcapWord := hbudget cap (by unfold LightLocalCoverCandidate.word LightPairFlags.word; omega)
  have hWWord :=
    hbudget (2 * L)
      (by
        unfold LightLocalCoverCandidate.word LightWeightDecode.word LightWeightRow.word
        omega)
  have h2Word := hbudget 2 (by unfold LightLocalCoverCandidate.word LightPairFlags.word; omega)
  have hWWordZ : (2 : ℤ) * L ≤ lim.word := by exact_mod_cast hWWord
  have hp2Word := hbudget (p * p) (by unfold LightLocalCoverCandidate.word LightPairFlags.word; omega)
  have hp2WordZ : (p : ℤ) * p ≤ lim.word := by exact_mod_cast hp2Word
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
    refine _root_.Light.Ends.setToThen (p * p : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightLocalCoverCandidate.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightLocalCoverCandidate.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightLocalCoverCandidate.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.for (Inv μ L n p cap N masks bitPtr maps raw0 raw1 hist0 hist1 dst work mask bits w0 w1) N
      (LightLocalCoverCandidate.time L n p N + 192) ?_ ?_ ?_ ?_ (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightLocalCoverCandidate.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightLocalCoverCandidate.time] <;> first
            | omega
            | (ring_nf; omega)))
  · refine ⟨0, μ, ?_, ?_, fun _ _ => rfl⟩
    · simp [update_frame_setLocal]
    · intro j hj; omega
  · rintro i _ hi _ ⟨r, μ', rfl, written, kept⟩
    have himaps := Nat.mul_le_mul_right (2 * L) (show i + 1 ≤ N by omega)
    have hihist := Nat.mul_le_mul_right p (show i + 1 ≤ N by omega)
    have himatrix := Nat.mul_le_mul_right (p * p) (show i + 1 ≤ N by omega)
    simp only [Nat.add_mul, one_mul] at himaps hihist himatrix
    have hcoef : maps + i * (2 * L) + 2 * L ≤ raw0 := by omega
    have hlhist : hist0 + i * p + p ≤ hist1 + i * p := by omega
    have hrhist : hist1 + i * p + p ≤ dst + i * (p * p) := by omega
    have hrow : dst + i * (p * p) + p * p ≤ work := by omega
    have hmulCoef : ((i * (2 * L) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (by omega : i * (2 * L) ≤ lim.space)).trans hw
    have hmulHist : ((i * p : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : i * p ≤ lim.space)).trans hw
    have hmulMatrix : ((i * (p * p) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (by omega : i * (p * p) ≤ lim.space)).trans hw
    have hcoefAddr : ((maps : ℤ) + (i : ℤ) * (2 * (L : ℤ))).toNat = maps + i * (2 * L) := by norm_cast
    have hlhistAddr : ((hist0 : ℤ) + (i : ℤ) * p).toNat = hist0 + i * p := by norm_cast
    have hrhistAddr : ((hist1 : ℤ) + (i : ℤ) * p).toNat = hist1 + i * p := by norm_cast
    have hmatrixAddr : ((dst : ℤ) + (i : ℤ) * ((p : ℤ) * p)).toNat = dst + i * (p * p) := by norm_cast
    have hmask' : ∀ j < n, μ' (masks + j) = (mask j : ℤ) :=
      by
      intro j hj
      rw [kept _ (by omega)]
      exact hmaskRead j hj
    have hbits' : ∀ a < n, ∀ j < L, μ' (bitPtr + a * L + j) = (bits a j : ℤ) :=
      by
      intro a ha j hj
      have hm := Nat.mul_le_mul_right L (show a + 1 ≤ n by omega)
      simp only [Nat.add_mul, one_mul] at hm
      have hab : bitPtr + a * L + j < maps := by omega
      rw [kept _ hab]
      exact hbitsRead a ha j hj
    have hword' : (LightLocalCoverCandidate.word L n p cap i : ℤ) ≤ lim.word :=
      by
      apply hbudget
      unfold LightLocalCoverCandidate.word LightWeightDecode.word LightWeightRow.word
      omega
    have htime' : LightLocalCoverCandidate.time L n p i ≤ LightLocalCoverCandidate.time L n p N :=
      by
      unfold LightLocalCoverCandidate.time LightWeightDecode.time LightWeightRow.time LightRadixDigit.time
      gcongr
    have hcall :=
      S.candidate.meets (d := d + 1) (μ := μ') (L := L) (n := n) (p := p) (cap := cap) (index := i) (masks := masks)
        (bitPtr := bitPtr) (coef := maps + i * (2 * L)) (raw0 := raw0) (raw1 := raw1) (hist0 := hist0 + i * p) (hist1 :=
        hist1 + i * p) (dst := dst + i * (p * p)) (work := work) mask (w0 i) (w1 i) bits hw (by omega) hp hn hspace
        (by omega) (by omega) hcoef hraw0 (by omega) hlhist hrhist hrow hword' hmask' hmaskLt hbits' hbitsValue
        (hw0 i hi) (hw1 i hi)
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
      | refine _root_.Light.Ends.callToThen ((hcall.mono_time htime') _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen (hcall.mono_time htime') ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcoefAddr,
              hlhistAddr, hrhistAddr, hmatrixAddr, LightLocalCoverCandidate.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hcoefAddr, hlhistAddr, hrhistAddr, hmatrixAddr, LightLocalCoverCandidate.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcoefAddr, hlhistAddr, hrhistAddr,
              hmatrixAddr, LightLocalCoverCandidate.time] <;> omega)
      on_goal -1 =>
        (rintro value μ₁ ⟨hcoeffs, hcounts, hentry, hpres⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hprevCoef : ∀ j < i, ∀ a < 2 * L, μ₁ (maps + j * (2 * L) + a) = μ' (maps + j * (2 * L) + a) :=
      by
      intro j hj a ha
      have hjm := Nat.mul_le_mul_right (2 * L) (show j + 1 ≤ i by omega)
      simp only [Nat.add_mul, one_mul] at hjm
      have hbefore : maps + j * (2 * L) + a < maps + i * (2 * L) := by omega
      exact
        hpres _ (by omega) (Or.inl hbefore) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
          (Or.inl (by omega)) (Or.inl (by omega))
    have hprevLeft : ∀ j < i, ∀ a < p, μ₁ (hist0 + j * p + a) = μ' (hist0 + j * p + a) :=
      by
      intro j hj a ha
      have hjm := Nat.mul_le_mul_right p (show j + 1 ≤ i by omega)
      simp only [Nat.add_mul, one_mul] at hjm
      have hbefore : hist0 + j * p + a < hist0 + i * p := by omega
      have hbound : hist0 + j * p + a < hist1 := by omega
      exact
        hpres _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl hbefore)
          (Or.inl (by omega)) (Or.inl (by omega))
    have hprevRight : ∀ j < i, ∀ a < p, μ₁ (hist1 + j * p + a) = μ' (hist1 + j * p + a) :=
      by
      intro j hj a ha
      have hjm := Nat.mul_le_mul_right p (show j + 1 ≤ i by omega)
      simp only [Nat.add_mul, one_mul] at hjm
      have hbefore : hist1 + j * p + a < hist1 + i * p := by omega
      have hbound : hist1 + j * p + a < dst := by omega
      have hleft : hist0 + i * p + p ≤ hist1 := by omega
      exact
        hpres _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
          (Or.inl hbefore) (Or.inl (by omega))
    have hprevMatrix : ∀ j < i, ∀ a < p * p, μ₁ (dst + j * (p * p) + a) = μ' (dst + j * (p * p) + a) :=
      by
      intro j hj a ha
      have hjm := Nat.mul_le_mul_right (p * p) (show j + 1 ≤ i by omega)
      simp only [Nat.add_mul, one_mul] at hjm
      have hbefore : dst + j * (p * p) + a < dst + i * (p * p) := by omega
      have hleft : hist0 + i * p + p ≤ hist1 := by omega
      have hright : hist1 + i * p + p ≤ dst := by omega
      exact
        hpres _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
          (Or.inr (by omega)) (Or.inl hbefore)
    refine ⟨by simp, value, μ₁, by simp [update_frame_setLocal], ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · obtain ⟨hc, hh, he⟩ := written j hj
        refine ⟨?_, ?_, ?_⟩
        · intro a ha
          constructor
          · rw [hprevCoef j hj a (by omega)]
            exact (hc a ha).1
          · have ha' : L + a < 2 * L := by omega
            have hkeep := hprevCoef j hj (L + a) ha'
            rw [← Nat.add_assoc] at hkeep
            rw [hkeep]
            exact (hc a ha).2
        · intro a ha
          rw [hprevLeft j hj a ha, hprevRight j hj a ha]
          exact hh a ha
        · intro a ha
          rw [hprevMatrix j hj a ha]
          exact he a ha
      · exact ⟨hcoeffs, hcounts, hentry⟩
    · intro a ha
      rw [hpres a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
          (Or.inl (by omega)) (Or.inl (by omega))]
      exact kept a ha
  · rintro _ _ ⟨r, μ', rfl, written, kept⟩
    exact ⟨written, kept⟩
  · rintro i _ _ _ ⟨r, μ', rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end Procs
end ThreeSum.LightLocalCoverMatrix
