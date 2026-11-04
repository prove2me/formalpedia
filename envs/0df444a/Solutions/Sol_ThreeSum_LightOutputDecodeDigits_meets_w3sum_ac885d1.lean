-- Prove2me | solution 1 for ThreeSum.LightOutputDecodeDigits.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:25:11.603822+00:00
-- url     : https://prove2.me/submissions/dad653ba-f8cb-4cbf-9754-0e78b2320f36

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDivide
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_frame_append_zeros
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
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_bounded_meets
import Definitions.Def_WeightedCache3SUM_Alias_5d4b5ec466dc091a
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
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightOutputDecodeDigits
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {k J m dst work V : ℕ}
namespace ThreeSum.LightOutputDecodeDigits
theorem _root_.solution {pMain pDivide : ℕ} (hmain : P[pMain]? = some (body pDivide))
    (hdivide : P[pDivide]? = some LightOutputDecodeDivide.body) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 1 < lim.depth) (hm : 1 ≤ m) (hk : k ≤ V) (hsep : dst + J ≤ work) (hspace : space work V ≤ lim.space)
    (hword : (word V m J : ℤ) ≤ lim.word) :
    Meets lim P pMain d [k, J, m, dst, work] μ (time J V)
      (fun r ν =>
        r = ((k / m ^ J : ℕ) : ℤ) ∧
          (∀ j < J, ν (dst + j) = ((OutputDecodeOrder.indices m J k).getD j 0 : ℤ)) ∧ Kept μ ν dst) :=
  by
  have hbudget (x : ℕ) (hx : x ≤ word V m J) : (x : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hx).trans hword
  have hVWord := hbudget V (by unfold word; omega)
  have hkWord : (k : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hk).trans hVWord
  have hmWord := hbudget m (by unfold word; omega)
  have hJWord := hbudget J (by unfold word; omega)
  have h1Word := hbudget 1 (by unfold word; omega)
  have hwork : work ≤ lim.space := by unfold space at hspace; omega
  have hfr : Light.Emod.Pre lim m V work := by
    refine ⟨hm, hw, ?_, hspace⟩
    have hh := hbudget (4 * V + 4 * m + 16) (by unfold word; omega)
    exact_mod_cast hh
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
    refine _root_.Light.Ends.setToThen (k : ℕ) ?_ ?_ ?_
    on_goal -1 =>
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
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.pieceThen
      (Ends.for (T := J * (LightOutputDecodeDivide.budget V + 100) + 6) (Q := Inv μ k J m dst work J)
        (Inv μ k J m dst work) J (LightOutputDecodeDivide.budget V + 92) ?start ?round ?done ?bound)
      ?finish
  case start =>
    refine ⟨0, 0, μ, ?_, ?_, SameOn.refl⟩
    · simp only [pow_zero, Nat.div_one]
      exact
        congrArg (fun loc => (⟨loc, μ⟩ : State))
          ((update_frame_setLocal [k, J, m, dst, work, k] 6 0).trans
            (frame_append_zeros [k, J, m, dst, work, k, 0] 2).symm)
    · intro j hj; omega
  case round =>
    rintro i _ hi _ ⟨q, r, ν, rfl, written, kept⟩
    have hrun : k / m ^ i ≤ V := (Nat.div_le_self _ _).trans hk
    have hqle : (k / m ^ i) / m ≤ k / m ^ i := Nat.div_le_self _ _
    have hrem : (k / m ^ i) % m ≤ V := (Nat.mod_le _ _).trans hrun
    have heq : (k / m ^ i) / m = k / m ^ (i + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
    have hdecomp := Nat.div_add_mod (k / m ^ i) m
    have hprod : ((k / m ^ i) / m) * m ≤ V := by rw [Nat.mul_comm]; omega
    have hprodWord : (((k / m ^ i) / m : ℕ) : ℤ) * (m : ℤ) ≤ lim.word :=
      (by exact_mod_cast hprod : (((k / m ^ i) / m : ℕ) : ℤ) * (m : ℤ) ≤ (V : ℤ)).trans hVWord
    have hprodNonneg : (0 : ℤ) ≤ (((k / m ^ i) / m : ℕ) : ℤ) * (m : ℤ) := by positivity
    have hprodWord' : (k : ℤ) / (m : ℤ) ^ i / (m : ℤ) * (m : ℤ) ≤ lim.word := by exact_mod_cast hprodWord
    have hprodNonneg' : (0 : ℤ) ≤ (k : ℤ) / (m : ℤ) ^ i / (m : ℤ) * (m : ℤ) := by positivity
    have hcurrentWord : (k : ℤ) / (m : ℤ) ^ i ≤ lim.word := by exact_mod_cast (Int.ofNat_le.mpr hrun).trans hVWord
    have hcurrentNonneg : (0 : ℤ) ≤ (k : ℤ) / (m : ℤ) ^ i := by positivity
    have hremWord' : (k : ℤ) / (m : ℤ) ^ i % (m : ℤ) ≤ lim.word := by
      exact_mod_cast (Int.ofNat_le.mpr hrem).trans hVWord
    have hremNonneg' : (0 : ℤ) ≤ (k : ℤ) / (m : ℤ) ^ i % (m : ℤ) := Int.emod_nonneg _ (by omega)
    have hdiff : ((k / m ^ i : ℕ) : ℤ) - (((k / m ^ i) / m : ℕ) : ℤ) * (m : ℤ) = (((k / m ^ i) % m : ℕ) : ℤ) :=
      by
      have hh : (m : ℤ) * (((k / m ^ i) / m : ℕ) : ℤ) + (((k / m ^ i) % m : ℕ) : ℤ) = ((k / m ^ i : ℕ) : ℤ) := by
        exact_mod_cast hdecomp
      nlinarith
    have hdiff' : (k : ℤ) / (m : ℤ) ^ i - (k : ℤ) / (m : ℤ) ^ i / (m : ℤ) * (m : ℤ) = (((k / m ^ i) % m : ℕ) : ℤ) := by
      exact_mod_cast hdiff
    have haddr : (dst : ℤ) + (J : ℤ) - 1 - (i : ℤ) = ((dst + J - 1 - i : ℕ) : ℤ) := by omega
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
            ((LightOutputDecodeDivide.bounded_meets (d := d + 1) hdivide hfr hrun) _ (by omega)) ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen (LightOutputDecodeDivide.bounded_meets (d := d + 1) hdivide hfr hrun) ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      on_goal -1 => (rintro value ν₁ ⟨hv, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen ((k / m ^ i) % m : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hv, hdiff, hdiff']
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hv, hdiff, hdiff'] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hv, hdiff, hdiff'] <;> omega)
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
      refine _root_.Light.Ends.storeToThen (dst + J - 1 - i) ((k / m ^ i) % m : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, haddr]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [haddr] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haddr] <;> omega)
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
      refine _root_.Light.Ends.setToThen (k / m ^ (i + 1) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hv, heq]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hv, heq] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hv, heq] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine
      ⟨by simp, value, ((k / m ^ i) % m : ℕ), Function.update ν₁ (dst + J - 1 - i) (((k / m ^ i) % m : ℕ) : ℤ), by
        simp [update_frame_setLocal], ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega), hkeep _ (by omega)]
        exact written j hj
      · simp
    · intro a ha
      rw [Function.update_of_ne (by omega), hkeep _ (by omega), kept _ ha]
  case done =>
    rintro _ _ ⟨q, r, ν, rfl, written, kept⟩
    exact ⟨q, r, ν, rfl, written, kept⟩
  case bound =>
    rintro i _ _ _ ⟨q, r, ν, rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case finish =>
    rintro _ ⟨q, r, ν, rfl, written, kept⟩
    have hrun : k / m ^ J ≤ V := (Nat.div_le_self _ _).trans hk
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (k / m ^ J : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨rfl, ?_, kept⟩
    intro j hj
    have ht : J - 1 - j < J := by omega
    have he := OutputDecodeOrder.indices_getD_reverse m J k ht
    have hwritten := written (J - 1 - j) ht
    have hcoord : J - 1 - (J - 1 - j) = j := by omega
    have haddress : dst + J - 1 - (J - 1 - j) = dst + j := by omega
    rw [hcoord] at he
    rw [haddress] at hwritten
    simpa only [he] using hwritten
end ThreeSum.LightOutputDecodeDigits
