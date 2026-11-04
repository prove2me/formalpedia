-- Prove2me | solution 1 for ThreeSum.LightTernaryCarryCodes.table_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:38:27.515202+00:00
-- url     : https://prove2.me/submissions/7201e4a0-e753-4597-81c3-ae99aaabc62a

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Theorems.Thm_ThreeSum_LightTernaryCarryCodes_row_meets
import Theorems.Thm_Light_Ends_pieceThen
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
import Theorems.Thm_ThreeSum_LightPascal_row_meets
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
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
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCarryCodes
open Light TernarySignedDigits
set_option maxHeartbeats 2400000
set_option maxRecDepth 9000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
namespace ThreeSum.LightTernaryCarryCodes
theorem _root_.solution {pTable pRow pDecode pDivide Q J dst work : ℕ} (htable : P[pTable]? = some (tableBody pRow))
    (hrow : P[pRow]? = some (rowBody pDecode)) (hdecode : P[pDecode]? = some (LightOutputDecodeDigits.body pDivide))
    (hdivide : P[pDivide]? = some LightOutputDecodeDivide.body) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 3 < lim.depth) (hsep : dst + Q * (J + 1) ≤ work) (hspace : space work Q ≤ lim.space)
    (hword : (word J Q : ℤ) ≤ lim.word) :
    Meets lim P pTable d [Q, J, dst, work] μ (tableTime Q J)
      (fun r ν => r = (Q : ℤ) ∧ Table ν dst J Q ∧ Kept μ ν dst) :=
  by
  have hwork : work ≤ lim.space := by unfold space LightOutputDecodeDigits.space at hspace; omega
  have hQWord : (Q : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word LightOutputDecodeDigits.word; omega : Q ≤ word J Q)).trans hword
  have hJWord : (J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word LightOutputDecodeDigits.word; omega : J ≤ word J Q)).trans hword
  have h1Word : (1 : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word LightOutputDecodeDigits.word; omega : 1 ≤ word J Q)).trans hword
  have hJ1Word : (J : ℤ) + 1 ≤ lim.word :=
    by
    have hh : ((J + 1 : ℕ) : ℤ) ≤ (word J Q : ℤ) :=
      Int.ofNat_le.mpr (by unfold word LightOutputDecodeDigits.word; omega)
    exact_mod_cast hh.trans hword
  apply Meets.of_body htable
  unfold tableBody tableTime
  refine
    Ends.pieceThen
      (Ends.for (T := Q * (rowTime J Q + 100) + 10) (Q := TableInv μ Q J dst work Q) (TableInv μ Q J dst work) Q
        (rowTime J Q + 80) ?start ?round ?done ?bound)
      ?finish
  case start =>
    refine ⟨0, μ, ?_, ?_, SameOn.refl⟩
    · simp only [update_frame_setLocal]
      exact congrArg (fun loc => (⟨loc, μ⟩ : State)) (frame_append_zeros [(Q : ℤ), J, dst, work, 0] 1).symm
    · intro q hq; omega
  case round =>
    rintro i _ hi _ ⟨r, ν, rfl, hrows, hkeep⟩
    have hstride : (i + 1) * (J + 1) ≤ Q * (J + 1) := Nat.mul_le_mul_right (J + 1) (by omega)
    have hlast : dst + i * (J + 1) + J + 1 ≤ work :=
      by
      simp only [Nat.add_mul, one_mul] at hstride
      omega
    have hprod : i * (J + 1) ≤ lim.space := by omega
    have hprodWord : (i : ℤ) * ((J : ℤ) + 1) ≤ lim.word := by exact_mod_cast ((Int.ofNat_le.mpr hprod).trans hw)
    have hprodNonneg : (0 : ℤ) ≤ (i : ℤ) * ((J : ℤ) + 1) := by positivity
    have haddrWord : (dst : ℤ) + (i : ℤ) * ((J : ℤ) + 1) ≤ lim.word := by
      exact_mod_cast ((Int.ofNat_le.mpr (show dst + i * (J + 1) ≤ lim.space by omega)).trans hw)
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
            ((row_meets (d := d + 1) (q := i) (J := J) (dst := dst + i * (J + 1)) (work := work) (V := Q) hrow hdecode
                hdivide hw (by omega) (by omega) hlast hspace hword)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen
            (row_meets (d := d + 1) (q := i) (J := J) (dst := dst + i * (J + 1)) (work := work) (V := Q) hrow hdecode
              hdivide hw (by omega) (by omega) hlast hspace hword)
            ?_ ?_ ?_ ?_
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
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      on_goal -1 => (rintro ret ξ ⟨hret, hnew, hpres⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, ret, ξ, by simp [update_frame_setLocal], ?_, ?_⟩
    · intro q hq
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
      · have hstrideq : (q + 1) * (J + 1) ≤ i * (J + 1) := Nat.mul_le_mul_right (J + 1) (by omega)
        simp only [Nat.add_mul, one_mul] at hstrideq
        have hold := hrows q hq
        refine ⟨?_, ?_⟩
        · rw [hpres _ (by omega)]
          exact hold.1
        · intro j hj
          rw [hpres _ (by omega)]
          exact hold.2 j hj
      · exact hnew
    · intro a ha
      rw [hpres _ (by omega), hkeep _ ha]
  case done =>
    rintro _ _ ⟨r, ν, rfl, hrows, hkeep⟩
    exact ⟨r, ν, rfl, hrows, hkeep⟩
  case bound =>
    rintro i _ hi _ ⟨r, ν, rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case finish =>
    rintro _ ⟨r, ν, rfl, hrows, hkeep⟩
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (Q : ℕ) ?_ ?_ ?_
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
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨rfl, hrows, hkeep⟩
end ThreeSum.LightTernaryCarryCodes
