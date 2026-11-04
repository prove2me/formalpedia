-- Prove2me | solution 1 for ThreeSum.LightColorArray.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:42:03.91924+00:00
-- url     : https://prove2.me/submissions/784c6f65-a8a9-43d0-9ace-e6a48a5792b9

import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightColorArray
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_powTable_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightColorIndex_color_lt
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightSubsetAddress_powers_of_segment
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
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightColorArray
open Light LightSubsetAddress
set_option maxHeartbeats 1200000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightColorArray
theorem _root_.solution {pMain pPowers pColor pErase W n dst work : ℕ} (hmain : P[pMain]? = some (body pPowers pColor))
    (hpowers : P[pPowers]? = some powTableBody) (hcolor : P[pColor]? = some (LightColorIndex.body pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase)) (μ : ℕ → ℤ) (p : Coloring.Parameter W)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2 ^ W) (hdst : dst + n ≤ work) (hspace : work + (W + 1) ≤ lim.space)
    (hword : ((2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word) (hd : d + W + 2 ≤ lim.depth) :
    Meets lim P pMain d
      [W, n, p.1.1.val, p.1.2.val, (p.2 (false, false)).val, (p.2 (false, true)).val, (p.2 (true, false)).val,
        (p.2 (true, true)).val, dst, work]
      μ (time W n)
      (fun _ ν =>
        (∀ i < n, ν (dst + i) = (LightColorIndex.color p i : ℤ)) ∧ Powers ν work W ∧ KeptBut μ ν work dst n) :=
  by
  have htwo : (2 : ℤ) ≤ lim.word :=
    by
    have hh : 2 ^ 1 ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast hh : (2 : ℤ) ≤ ((2 ^ (W + 1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body hmain
  unfold body time
  have hp :=
    powTable_meets (d := d + 1) (μ := μ) (dst := work) (L := W + 1) (b := 2) hpowers hw hspace
      (by
        intro i hi
        exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hi)).trans hword)
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
    | refine _root_.Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hp ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightColorIndex.time, LightMaskErase.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightColorIndex.time, LightMaskErase.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightColorIndex.time, LightMaskErase.time] <;>
          omega)
    on_goal -1 => (rintro powRet ν₀ ⟨pow, keep₀⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have pow₀ : Powers ν₀ work W := powers_of_segment pow
  refine
    Ends.for (Inv μ p n dst work powRet) n (LightColorIndex.time W + 90) ?start ?round ?done ?bound (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightColorIndex.time, LightMaskErase.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightColorIndex.time, LightMaskErase.time] <;>
            first
            | omega
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, ν₀, ?_, ?_, pow₀, ?_⟩
    · simp [update_frame_setLocal]
      exact (frame_append_zeros _ 1).symm
    · intro i hi
      omega
    · intro a ha
      exact keep₀ a (Or.inl ha.1)
  case round =>
    rintro j _ hj _ ⟨r, ν, rfl, written, pows, kept⟩
    have hc :=
      LightColorIndex.meets (d := d + 1) (m := j) (powers := work) hcolor herase ν p hw hspace hword pows (by omega)
        (by omega)
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
              LightColorIndex.time, LightMaskErase.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightColorIndex.time, LightMaskErase.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightColorIndex.time, LightMaskErase.time] <;>
            omega)
      on_goal -1 => (rintro r' ν' ⟨hr, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ν'
    have hcLt := LightColorIndex.color_lt p j
    have hcWord : (LightColorIndex.color p j : ℤ) ≤ lim.word := by omega
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + j) (LightColorIndex.color p j : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr,
              LightColorIndex.time, LightMaskErase.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hr, LightColorIndex.time, LightMaskErase.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr, LightColorIndex.time,
              LightMaskErase.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine
      ⟨by simp, r', Function.update ν (dst + j) (LightColorIndex.color p j : ℤ), by simp [update_frame_setLocal], ?_,
        ?_, ?_⟩
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [Function.update_of_ne (by omega)]
        exact written i hi
      · simp
    · intro i hi
      rw [Function.update_of_ne (by omega)]
      exact pows i hi
    · intro a ha
      rw [Function.update_of_ne (by omega)]
      exact kept a ha
  case done =>
    rintro _ _ ⟨r, ν, rfl, written, pows, kept⟩
    exact ⟨written, pows, kept⟩
  case bound =>
    rintro j _ hj _ ⟨r, ν, rfl, _, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightColorArray
