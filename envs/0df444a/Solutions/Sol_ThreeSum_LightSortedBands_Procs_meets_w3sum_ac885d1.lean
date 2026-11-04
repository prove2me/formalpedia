-- Prove2me | solution 1 for ThreeSum.LightSortedBands.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:18.332063+00:00
-- url     : https://prove2.me/submissions/3d7794a4-4119-4131-a63b-ef688e749193

import Definitions.Def_Submission_ThreeSum_LightNormalize
import Definitions.Def_Submission_ThreeSum_LightBandPartition
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_mono_time
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
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
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Theorems.Thm_ThreeSum_LightBandEnumeration_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_fecb00c51dea7534
import Theorems.Thm_ThreeSum_LightBandPartition_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Definitions.Def_WeightedCache3SUM_Alias_d98593d0ef804094
import Theorems.Thm_ThreeSum_LightNormalize_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
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
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightSortedBands
open Light ThreeSum.BandPartition
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSortedBands
namespace Procs
theorem _root_.solution {pMain src values endpoints work g d : ℕ} {μ : ℕ → ℤ} {original : List ℤ} (R : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g) (hsrc : src + original.length ≤ values)
    (hvalues : values + original.length ≤ endpoints) (hendpoints : endpoints + 2 + 2 * original.length ≤ work)
    (hspace : space work original.length ≤ lim.space) (hword : ((original.length + g + 2 : ℕ) : ℤ) ≤ lim.word)
    (hd : d + original.length + Nat.clog 2 original.length + 3 ≤ lim.depth) (hread : Seg μ src original) :
    Meets lim P pMain d [src, original.length, g, values, endpoints, work] μ (time original.length)
      (fun r μ' =>
        r = μ' (endpoints + 1) ∧
          Prepared μ' values endpoints g original ∧
            ∀ a,
              a < work →
                (a < src ∨ src + original.length ≤ a) →
                  (a < values ∨ values + original.length ≤ a) →
                    (a < endpoints ∨ endpoints + 2 + 2 * original.length ≤ a) → μ' a = μ a) :=
  by
  have h1 : (1 : ℤ) ≤ lim.word := by omega
  have hspace' : work + original.length ≤ lim.space := hspace
  apply Meets.of_body R.main
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
          ((R.normalize.meets (d := d + 1) (src := src) (dst := values) (work := work) hw h1 hread hsrc (by omega)
              hspace (by omega))
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (R.normalize.meets (d := d + 1) (src := src) (dst := values) (work := work) hw h1 hread hsrc (by omega) hspace
            (by omega))
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightNormalize.time, sortTime,
            LightNormalize.dedupTime, space]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightNormalize.time, sortTime, LightNormalize.dedupTime, space] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightNormalize.time, sortTime,
            LightNormalize.dedupTime, space] <;> omega)
    on_goal -1 =>
      (rintro len μ₁ ⟨L, hlen, hL, hstrict, hcount, hmem, hkept₁⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hLread : ∀ i < L.length, μ₁ (values + i) = L.getD i 0 :=
    by
    intro i hi
    exact hL.getD hi 0
  have hpart :=
    LightBandPartition.meets (d := d + 1) (src := values) (dst := endpoints + 2) R.partition R.divide R.lower R.upper μ₁
      (fun i => L.getD i 0) hw hg (by omega) (by unfold space at hspace; omega)
      ((Int.ofNat_le.mpr (by omega : L.length + g + 2 ≤ original.length + g + 2)).trans hword) hLread (by omega)
  have hpartTime : LightBandPartition.time L.length g ≤ 200 * original.length + 200 :=
    (LightBandPartition.time_bound _ _).trans (by omega)
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
    | refine _root_.Light.Ends.callToThen ((hpart.mono_time hpartTime) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (hpart.mono_time hpartTime) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlen, LightNormalize.time, sortTime,
            LightNormalize.dedupTime, space]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hlen, LightNormalize.time, sortTime, LightNormalize.dedupTime, space] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlen, LightNormalize.time, sortTime,
            LightNormalize.dedupTime, space] <;> omega)
    on_goal -1 => (rintro bands μ₂ ⟨hbands, hlo, hhi, hkept₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hL₂ : Seg μ₂ values L := by
    intro i hi
    rw [hkept₂ (values + i) (Or.inl (by omega))]
    exact hL i hi
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen endpoints (L.length : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlen, LightNormalize.time, sortTime,
            LightNormalize.dedupTime, space]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hlen, LightNormalize.time, sortTime, LightNormalize.dedupTime, space] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlen, LightNormalize.time, sortTime,
            LightNormalize.dedupTime, space] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (endpoints + 1) (size L.length g : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbands, LightNormalize.time, sortTime,
            LightNormalize.dedupTime, space]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hbands, LightNormalize.time, sortTime, LightNormalize.dedupTime, space] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbands, LightNormalize.time, sortTime,
            LightNormalize.dedupTime, space] <;> omega)
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
    refine _root_.Light.Ends.setToThen (size L.length g : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbands, LightNormalize.time, sortTime,
            LightNormalize.dedupTime, space]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hbands, LightNormalize.time, sortTime, LightNormalize.dedupTime, space] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbands, LightNormalize.time, sortTime,
            LightNormalize.dedupTime, space] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨by simp, ⟨L, ?_, hstrict, hcount, hmem, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    change
      Function.update (Function.update μ₂ endpoints (L.length : ℤ)) (endpoints + 1) (size L.length g : ℤ) (values + i) =
        _
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hL₂ i hi
  · simp
  · simp
  · intro i hi
    change
      Function.update (Function.update μ₂ endpoints (L.length : ℤ)) (endpoints + 1) (size L.length g : ℤ)
          (endpoints + 2 + i) =
        _
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hlo i hi
  · intro i hi
    change
      Function.update (Function.update μ₂ endpoints (L.length : ℤ)) (endpoints + 1) (size L.length g : ℤ)
          (endpoints + 2 + L.length + i) =
        _
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hhi i hi
  · intro a ha hsrc hvalues hendpoints
    change Function.update (Function.update μ₂ endpoints (L.length : ℤ)) (endpoints + 1) (size L.length g : ℤ) a = _
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hkept₂ a (by omega)]
    exact hkept₁ a ha hsrc hvalues
end Procs
end ThreeSum.LightSortedBands
