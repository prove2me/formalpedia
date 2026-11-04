-- Prove2me | solution 1 for ThreeSum.LightTernarySignedRow.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:34:26.674737+00:00
-- url     : https://prove2.me/submissions/cdd1d648-9b86-45d8-9368-d4eec7756408

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_Light_wrote_done
import Theorems.Thm_Light_wrote_rest
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_OutputDecodeOrder_indices_getD_lt
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
open ThreeSum ThreeSum.LightTernarySignedRow
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernarySignedRow
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ} {J radix dst work V value offset : ℕ}
    {x sign tag0 tag1 : ℤ} (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 2 < lim.depth) (hb : 1 ≤ radix)
    (hval : value ≤ V) (hshift : x + (offset : ℤ) = (value : ℤ)) (hx : |x| ≤ (V : ℤ)) (hoff : offset ≤ V)
    (hsign : |sign| ≤ 1) (ht0 : |tag0| ≤ 1) (ht1 : |tag1| ≤ 1) (hsep : dst + J + 2 ≤ work)
    (hspace : space work V ≤ lim.space) (hword : (word V radix J : ℤ) ≤ lim.word) :
    Meets lim P pMain d [x, offset, sign, J, radix, dst, work, tag0, tag1] μ (time J V)
      (fun _ ν =>
        (∀ j < J, ν (dst + j) = sign * ((OutputDecodeOrder.indices radix J value).getD j 0 : ℤ)) ∧
          ν (dst + J) = tag0 ∧ ν (dst + J + 1) = tag1 ∧ Kept μ ν dst) :=
  by
  have hbudget (z : ℕ) (hz : z ≤ word V radix J) : (z : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hz).trans hword
  have hV := hbudget V (by unfold word LightOutputDecodeDigits.word; omega)
  have hB := hbudget radix (by unfold word LightOutputDecodeDigits.word; omega)
  have hJ := hbudget J (by unfold word LightOutputDecodeDigits.word; omega)
  have h1 := hbudget 1 (by unfold word LightOutputDecodeDigits.word; omega)
  have hOff : (offset : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hoff).trans hV
  have hVal : (value : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hval).trans hV
  have hwork : work ≤ lim.space := by unfold space LightOutputDecodeDigits.space at hspace; omega
  have hdst : dst + J ≤ lim.space := by omega
  have hx' := abs_le.mp hx
  have hsign' := abs_le.mp hsign
  have ht0' := abs_le.mp ht0
  have ht1' := abs_le.mp ht1
  apply Meets.of_body S.main
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
    refine _root_.Light.Ends.setToThen (value : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hshift, LightOutputDecodeDigits.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hshift, LightOutputDecodeDigits.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hshift, LightOutputDecodeDigits.time] <;> omega)
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
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightOutputDecodeDigits.meets (d := d + 1) (μ := μ) (J := J) (m := radix) (k := value) (dst := dst) (work :=
              work) S.digits S.divide hw (by omega) hb hval (by omega) hspace hword)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightOutputDecodeDigits.meets (d := d + 1) (μ := μ) (J := J) (m := radix) (k := value) (dst := dst) (work :=
            work) S.digits S.divide hw (by omega) hb hval (by omega) hspace hword)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightOutputDecodeDigits.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightOutputDecodeDigits.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightOutputDecodeDigits.time] <;> omega)
    on_goal -1 => (rintro q ν ⟨hq, hread, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  let f : ℕ → ℤ := fun j => sign * ((OutputDecodeOrder.indices radix J value).getD j 0 : ℤ)
  refine
    Ends.pieceThen
      (Ends.pass (T := 30 * J + 10) (Q := fun σ =>
        σ =
          ⟨Function.update (frame (setLocal (setLocal [x, offset, sign, J, radix, dst, work, tag0, tag1] 9 value) 10 q))
              11 (J : ℤ),
            wrote ν dst f J⟩)
        f ?round ?done hw hdst rfl rfl)
      ?finish
  case round =>
    intro j hj
    have hlt := OutputDecodeOrder.indices_getD_lt (k := value) (show 0 < radix by omega) hj
    have hcell := hread j hj
    have hcur : wrote ν dst f j (dst + j) = ν (dst + j) := wrote_rest (by omega)
    have hcur' :
      wrote ν dst (fun j => sign * ((OutputDecodeOrder.indices radix J value).getD j 0 : ℤ)) j (dst + j) =
        ((OutputDecodeOrder.indices radix J value).getD j 0 : ℤ) :=
      hcur.trans hcell
    have hd0 : (0 : ℤ) ≤ (OutputDecodeOrder.indices radix J value).getD j 0 := by positivity
    have hdB : ((OutputDecodeOrder.indices radix J value).getD j 0 : ℤ) ≤ radix := by exact_mod_cast hlt.le
    have hprod : |sign * ((OutputDecodeOrder.indices radix J value).getD j 0 : ℤ)| ≤ lim.word :=
      by
      rw [abs_mul, abs_of_nonneg hd0]
      exact (mul_le_mul hsign hdB hd0 (by norm_num : (0 : ℤ) ≤ 1)).trans (by simpa using hB)
    have hprod' := abs_le.mp hprod
    simp only [List.getD_eq_getElem?_getD] at hcur' hprod' hcell hd0 hdB
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, f, hcur', hcell] <;> omega)
  case done => rfl
  case finish =>
    rintro _ rfl
    rw [update_frame_setLocal]
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + J) tag0 ?_ ?_ ?_
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
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + J + 1) tag1 ?_ ?_ ?_
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
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (0 : ℤ) ?_ ?_ ?_
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
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j hj
      dsimp only
      rw [Function.update_of_ne (show dst + j ≠ dst + J + 1 by omega),
        Function.update_of_ne (show dst + j ≠ dst + J by omega), wrote_done hj]
    · simp only [Function.update_of_ne (by omega : dst + J ≠ dst + J + 1), Function.update_self]
    · simp
    · intro a ha
      dsimp only
      rw [Function.update_of_ne (show a ≠ dst + J + 1 by omega), Function.update_of_ne (show a ≠ dst + J by omega),
        wrote_rest (by omega), hkeep a ha]
end Procs
end ThreeSum.LightTernarySignedRow
