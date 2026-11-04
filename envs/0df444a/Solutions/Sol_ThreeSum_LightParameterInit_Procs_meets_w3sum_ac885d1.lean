-- Prove2me | solution 1 for ThreeSum.LightParameterInit.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:20:41.808736+00:00
-- url     : https://prove2.me/submissions/d3fd0b9a-8c13-4cb0-b66d-bc9e90d5eb79

import Definitions.Def_Submission_ThreeSum_LightScales
import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_LightGlobalSizes
import Definitions.Def_Submission_ThreeSum_LightParameterInit
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
import Definitions.Def_WeightedCache3SUM_Alias_04c57512725a2a98
import Definitions.Def_WeightedCache3SUM_Alias_2e17023b917df3d1
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
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
import Definitions.Def_WeightedCache3SUM_Alias_3718d050d478b160
import Theorems.Thm_ThreeSum_LightGlobalSizes_localCount_pos
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Definitions.Def_WeightedCache3SUM_Alias_9f151fd16c06b1ef
import Definitions.Def_WeightedCache3SUM_Alias_e2ad5e59f3af6ab7
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Theorems.Thm_ThreeSum_LightPrimality_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_137b880911028d95
import Definitions.Def_WeightedCache3SUM_Alias_a00dee90c4e0ea45
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScales_Procs_meets
import Theorems.Thm_ThreeSum_LightScales_blockCount_le
import Theorems.Thm_ThreeSum_LightScales_inputBits_le_self
import Definitions.Def_WeightedCache3SUM_Alias_984013d7ba738e5d
import Theorems.Thm_ThreeSum_LightScales_microHalf_le_self
import Theorems.Thm_ThreeSum_LightScales_totalSize_le_self
import Definitions.Def_WeightedCache3SUM_Alias_276ab4baf5d9c1f3
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos
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
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
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
open ThreeSum ThreeSum.LightParameterInit
open Light LocalCoverBounds Scales
set_option maxHeartbeats 1500000
set_option maxRecDepth 5000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightParameterInit
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ} {n dst work : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 512 * half n + 6 ≤ lim.depth) (hout : dst + 19 ≤ work) (hspace : space work n ≤ lim.space)
    (hword : (word n : ℤ) ≤ lim.word) :
    Meets lim P pMain d [n, dst, work] μ (time n)
      (fun r μ' => r = (radix n : ℤ) ∧ Seg μ' dst (values n) ∧ KeptBut μ μ' work dst 19) :=
  by
  have hCoreWord : ((1000 * (n + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : 1000 * (n + 1) ≤ word n := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hLocalWord : (LightLocalParameters.word (half n) : ℤ) ≤ lim.word :=
    by
    have hh : LightLocalParameters.word (half n) ≤ word n := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hGlobalWord :
    (LightGlobalSizes.word (LightGlobalSizes.localCount n) (localRadix n) (blockCount (inputBits n)) (mu n) : ℤ) ≤
      lim.word :=
    by
    have hh :
      LightGlobalSizes.word (LightGlobalSizes.localCount n) (localRadix n) (blockCount (inputBits n)) (mu n) ≤ word n :=
      by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hAuxWord : ((100 * (primeWindow n + inputBits n + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : 100 * (primeWindow n + inputBits n + 1) ≤ word n := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwork : work ≤ lim.space :=
    by
    have hh : LightLocalCounts.space work (half n) ≤ lim.space := (le_max_left _ _).trans hspace
    unfold LightLocalCounts.space at hh
    omega
  have hbits := LightScales.inputBits_le_self n
  have hhalf : half n ≤ n := (LightScales.microHalf_le_self (inputBits n)).trans hbits
  have hmu : mu n ≤ n := (LightScales.totalSize_le_self (inputBits n)).trans hbits
  have hJ : blockCount (inputBits n) ≤ 20 * n := (LightScales.blockCount_le _).trans (Nat.mul_le_mul_left _ hbits)
  have hglobalBound (x : ℕ)
    (hx : x ≤ LightGlobalSizes.word (LightGlobalSizes.localCount n) (localRadix n) (blockCount (inputBits n)) (mu n)) :
    (x : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hx).trans hGlobalWord
  have hCWord := hglobalBound (LightGlobalSizes.localCount n) (by unfold LightGlobalSizes.word; omega)
  have hpWord := hglobalBound (localRadix n) (by unfold LightGlobalSizes.word; omega)
  have hRWord : (radix n : ℤ) ≤ lim.word := hglobalBound (radix n) (by unfold LightGlobalSizes.word radix; omega)
  have hWindowWord : (primeWindow n : ℤ) ≤ lim.word := by omega
  have hsqrt := Nat.sqrt_le_self (inputBits n)
  have he : windowExponent (inputBits n) ≤ inputBits n + 1 := by unfold windowExponent; omega
  have heWord : (windowExponent (inputBits n) : ℤ) ≤ lim.word := by omega
  have hWindowPowers (i : ℕ) (hi : i ≤ windowExponent (inputBits n)) : ((2 ^ i : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hi)).trans hWindowWord
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
          ((S.core.meets (d := d + 1) (μ := μ) (n := n) (dst := dst) hw (by omega) hCoreWord (by omega)) _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (S.core.meets (d := d + 1) (μ := μ) (n := n) (dst := dst) hw (by omega) hCoreWord (by omega)) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightNatPower.time] <;> omega)
    on_goal -1 => (rintro total μ₁ ⟨htotal, hcore, hkept₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hhalfRead : μ₁ (dst + 1) = (half n : ℤ) := by
    simpa [LightScales.values, half] using hcore 1 (by simp [LightScales.values])
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (half n : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hhalfRead, LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hhalfRead, LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hhalfRead, LightNatPower.time] <;> omega)
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
          ((S.localParams.meets (d := d + 1) (μ := μ₁) (h := half n) (dst := dst + 5) (work := work) hw (by omega)
              (by omega) hspace hLocalWord)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (S.localParams.meets (d := d + 1) (μ := μ₁) (h := half n) (dst := dst + 5) (work := work) hw (by omega)
            (by omega) hspace hLocalWord)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightNatPower.time] <;> omega)
    on_goal -1 => (rintro pval μ₂ ⟨hpval, hlocal, hkept₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hpval' : pval = (localRadix n : ℤ) := hpval
  have hcore₂ : Seg μ₂ dst (LightScales.values n) :=
    by
    apply hcore.congr
    intro i hi
    have hi' : i < 5 := by simpa [LightScales.values] using hi
    exact hkept₂ _ ⟨by omega, Or.inl (by omega)⟩
  have hprefix₂ : Seg μ₂ dst (LightScales.values n ++ LightLocalParameters.values (half n)) :=
    by
    apply seg_append.mpr
    exact ⟨hcore₂, by simpa [LightScales.values] using hlocal⟩
  have hJread : μ₂ (dst + 3) = (blockCount (inputBits n) : ℤ) := by
    simpa [LightScales.values] using hcore₂ 3 (by simp [LightScales.values])
  have hCread : μ₂ (dst + 5) = (LightGlobalSizes.localCount n : ℤ) := by
    simpa [LightLocalParameters.values, LightLocalCounts.values, half, LightGlobalSizes.localCount] using
      hlocal 0 (by simp [LightLocalParameters.values, LightLocalCounts.values])
  have hJnat : ((dst : ℤ) + 3).toNat = dst + 3 := by
    rw [show (dst : ℤ) + 3 = ((dst + 3 : ℕ) : ℤ) by omega, Int.toNat_natCast]
  have hCnat : ((dst : ℤ) + 5).toNat = dst + 5 := by
    rw [show (dst : ℤ) + 5 = ((dst + 5 : ℕ) : ℤ) by omega, Int.toNat_natCast]
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (blockCount (inputBits n) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hJnat, hJread, LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hJnat, hJread, LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hJnat, hJread, LightNatPower.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (LightGlobalSizes.localCount n : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hCnat, hCread, LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hCnat, hCread, LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hCnat, hCread, LightNatPower.time] <;> omega)
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
          ((S.globalSizes.meets (d := d + 1) (μ := μ₂) (C := LightGlobalSizes.localCount n) (p := localRadix n) (J :=
              blockCount (inputBits n)) (mu := mu n) (dst := dst + 13) hw (by omega) (LightGlobalSizes.localCount_pos n)
              (localPrime_pos (half n)) (by omega) hGlobalWord)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (S.globalSizes.meets (d := d + 1) (μ := μ₂) (C := LightGlobalSizes.localCount n) (p := localRadix n) (J :=
            blockCount (inputBits n)) (mu := mu n) (dst := dst + 13) hw (by omega) (LightGlobalSizes.localCount_pos n)
            (localPrime_pos (half n)) (by omega) hGlobalWord)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hpval', htotal, LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hpval', htotal, LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hpval', htotal, LightNatPower.time] <;> omega)
    on_goal -1 =>
      (rintro rglobal μ₃ ⟨hglobalResult, hglobal, hkept₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hglobalResult' : rglobal = (radix n : ℤ) := hglobalResult
  have hprefix₃ : Seg μ₃ dst (LightScales.values n ++ LightLocalParameters.values (half n)) :=
    by
    apply hprefix₂.congr
    intro i hi
    have hi' : i < 13 := by simpa [LightScales.values, LightLocalParameters.values, LightLocalCounts.values] using hi
    exact hkept₃ _ (Or.inl (by omega))
  have hfull :
    Seg μ₃ dst
      ((LightScales.values n ++ LightLocalParameters.values (half n)) ++
        LightGlobalSizes.values (LightGlobalSizes.localCount n) (localRadix n) (blockCount (inputBits n)) (mu n)) :=
    by
    apply seg_append.mpr
    exact ⟨hprefix₃, by simpa [LightScales.values, LightLocalParameters.values, LightLocalCounts.values] using hglobal⟩
  have hbitsRead : μ₃ dst = (inputBits n : ℤ) := by
    simpa [LightScales.values] using hprefix₃ 0 (by simp [LightScales.values])
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (inputBits n : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbitsRead, LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hbitsRead, LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbitsRead, LightNatPower.time] <;> omega)
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
        _root_.Light.Ends.callToThen ((sqrt_meets (d := d + 1) (K := inputBits n) S.sqrt μ₃ (by omega)) _ (by omega)) ?_
          ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (sqrt_meets (d := d + 1) (K := inputBits n) S.sqrt μ₃ (by omega)) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightNatPower.time] <;> omega)
    on_goal -1 => (rintro rt μ₄ ⟨hrt, hmem₄⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₄
  have hrt' : rt + 1 = (windowExponent (inputBits n) : ℤ) := by
    simpa [windowExponent] using congrArg (fun z : ℤ => z + 1) hrt
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (windowExponent (inputBits n) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrt', LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hrt', LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrt', LightNatPower.time] <;> omega)
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
          ((LightNatPower.meets (d := d + 1) (b := 2) (e := windowExponent (inputBits n)) S.power μ₃ heWord
              hWindowPowers)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightNatPower.meets (d := d + 1) (b := 2) (e := windowExponent (inputBits n)) S.power μ₃ heWord
            hWindowPowers)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightNatPower.time] <;> omega)
    on_goal -1 => (rintro window μ₅ ⟨hwindow, hmem₅⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₅
  have hwindow' : window = (primeWindow n : ℤ) := hwindow
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen (dst + 18) (primeWindow n : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hwindow', LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hwindow', LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hwindow', LightNatPower.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (radix n : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hglobalResult', LightNatPower.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hglobalResult', LightNatPower.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hglobalResult', LightNatPower.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨rfl, ?_, ?_⟩
  ·
    simpa [values, LightScales.values, LightLocalParameters.values, LightLocalCounts.values,
      LightGlobalSizes.values] using hfull.snoc (primeWindow n : ℤ)
  · intro a ha
    change Function.update μ₃ (dst + 18) _ a = μ a
    rw [Function.update_of_ne (by omega)]
    exact (hkept₃ a (by omega)).trans ((hkept₂ a ⟨ha.1, by omega⟩).trans (hkept₁ a (by omega)))
end Procs
end ThreeSum.LightParameterInit
