-- Prove2me | solution 1 for ThreeSum.LightLocalParameters.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:09:41.769196+00:00
-- url     : https://prove2.me/submissions/69311815-0aa4-4970-a6ba-253600e368b7

import Definitions.Def_Submission_ThreeSum_LightLocalCounts
import Definitions.Def_Submission_ThreeSum_LightSelectedPrime
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SegN_snoc
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_Light_Seg_snoc
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Definitions.Def_WeightedCache3SUM_Alias_9f151fd16c06b1ef
import Theorems.Thm_ThreeSum_LightPrimality_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_137b880911028d95
import Definitions.Def_WeightedCache3SUM_Alias_a00dee90c4e0ea45
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Definitions.Def_WeightedCache3SUM_Alias_276ab4baf5d9c1f3
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos
import Theorems.Thm_ThreeSum_LocalCoverBounds_localThreshold_pos
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_WeightedScore_corrections_zero
import Theorems.Thm_ThreeSum_WeightedScore_remaining_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.WeightedScore.corrections_zero
attribute [local simp] ThreeSum.WeightedScore.remaining_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalParameters
open Light LocalCoverBounds
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightLocalParameters
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ} {h dst work : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 512 * h + 5 ≤ lim.depth) (hout : dst + 8 ≤ work) (hspace : space work h ≤ lim.space)
    (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim P pMain d [h, dst, work] μ (time h)
      (fun r μ' => r = (localPrime h : ℤ) ∧ Seg μ' dst (values h) ∧ KeptBut μ μ' work dst 8) :=
  by
  have hcs : LightLocalCounts.space work h ≤ lim.space := (le_max_left _ _).trans hspace
  have hps : LightSelectedPrime.space work (localThreshold h) ≤ lim.space := (le_max_right _ _).trans hspace
  have hcw : (LightLocalCounts.word h : ℤ) ≤ lim.word :=
    by
    have hn : LightLocalCounts.word h ≤ word h := by unfold word; omega
    exact (Int.ofNat_le.mpr hn).trans hword
  have hpw : (LightSelectedPrime.word (localThreshold h) : ℤ) ≤ lim.word :=
    by
    have hn : LightSelectedPrime.word (localThreshold h) ≤ word h := by unfold word; omega
    exact (Int.ofNat_le.mpr hn).trans hword
  have hnumw : ((numerator h + localPrime h + 2 : ℕ) : ℤ) ≤ lim.word :=
    by
    have hn : numerator h + localPrime h + 2 ≤ word h := by unfold numerator word; omega
    exact (Int.ofNat_le.mpr hn).trans hword
  have hsmall : ((20 * (localPrime h + vertexCount (512 * h) h + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hn : 20 * (localPrime h + vertexCount (512 * h) h + 1) ≤ word h := by unfold word; omega
    exact (Int.ofNat_le.mpr hn).trans hword
  have hp := localPrime_pos h
  have hN := localThreshold_pos h
  have hwork : work ≤ lim.space := by unfold LightLocalCounts.space at hcs; omega
  have hhsize : 512 * h + 1 ≤ LightPascal.tableSize (512 * h) :=
    by
    unfold LightPascal.tableSize
    nlinarith
  have hh : h < lim.space := by unfold LightLocalCounts.space at hcs; omega
  have hNWord : (localThreshold h : ℤ) ≤ lim.word :=
    by
    have hh : 100 * ((localThreshold h : ℤ) + 1) ≤ lim.word := by simpa [LightSelectedPrime.word] using hpw
    omega
  have hnumEq :
    (4 : ℤ) * ((localPrime h : ℤ) + (vertexCount (512 * h) h : ℤ)) + (localPrime h : ℤ) - 1 = (numerator h : ℤ) := by
    unfold numerator; omega
  have hcapEq : numerator h / localPrime h = localBucketCap h := by rfl
  have hcapLe : localBucketCap h ≤ numerator h := by
    rw [← hcapEq]
    exact Nat.div_le_self _ _
  have hcapWord : (localBucketCap h : ℤ) ≤ lim.word := by omega
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
          ((S.counts.meets (d := d + 1) (μ := μ) (h := h) (dst := dst) (work := work) hw (by omega) (by omega) hcs hcw)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (S.counts.meets (d := d + 1) (μ := μ) (h := h) (dst := dst) (work := work) hw (by omega) (by omega) hcs hcw)
          ?_ ?_ ?_ ?_
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
    on_goal -1 => (rintro threshold μ₁ ⟨ht, hseg, hkept₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
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
          ((S.prime.meets (d := d + 1) (μ := μ₁) (N := localThreshold h) (free := work) hw (by omega) hN hps hpw) _
            (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (S.prime.meets (d := d + 1) (μ := μ₁) (N := localThreshold h) (free := work) hw (by omega) hN hps hpw) ?_ ?_
          ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ht]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [ht] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ht] <;> omega)
    on_goal -1 => (rintro pval μ₂ ⟨hpval, hpool, hkept₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hpval' : pval = (localPrime h : ℤ) := hpval
  have hseg₂ : Seg μ₂ dst (LightLocalCounts.values h) :=
    by
    apply hseg.congr
    intro i hi
    have hi' : i < 6 := by simpa [LightLocalCounts.values] using hi
    exact hkept₂ _ (by omega)
  have hvread : μ₂ (dst + 1) = (vertexCount (512 * h) h : ℤ) := by
    simpa [LightLocalCounts.values] using hseg₂ 1 (by simp [LightLocalCounts.values])
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (vertexCount (512 * h) h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hvread]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hvread] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hvread] <;> omega)
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
    refine _root_.Light.Ends.setToThen (numerator h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hpval', hnumEq]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hpval', hnumEq] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hpval', hnumEq] <;> omega)
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
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightSmallDivide.meets (d := d + 1) (a := numerator h) (b := localPrime h) S.divide μ₂ hnumw) _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightSmallDivide.meets (d := d + 1) (a := numerator h) (b := localPrime h) S.divide μ₂ hnumw) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hpval']
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hpval'] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hpval'] <;> omega)
    on_goal -1 => (rintro cap μ₃ ⟨hcap, hmem₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₃
  have hcap' : cap = (localBucketCap h : ℤ) := by simpa [hcapEq] using hcap
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen (dst + 6) (localPrime h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hpval']
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hpval'] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hpval'] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (dst + 7) (localBucketCap h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcap']
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hcap'] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcap'] <;> omega)
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
    refine _root_.Light.Ends.setToThen (localPrime h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hpval']
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hpval'] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hpval'] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨rfl, ?_, ?_⟩
  · simpa [values, LightLocalCounts.values] using ((hseg₂.snoc (localPrime h : ℤ)).snoc (localBucketCap h : ℤ))
  · intro a ha
    change Function.update (Function.update μ₂ (dst + 6) _) (dst + 7) _ a = μ a
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact (hkept₂ a ha.1).trans (hkept₁ a ⟨ha.1, by omega⟩)
end Procs
end ThreeSum.LightLocalParameters
