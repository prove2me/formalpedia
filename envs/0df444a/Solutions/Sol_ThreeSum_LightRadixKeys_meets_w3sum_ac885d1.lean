-- Prove2me | solution 1 for ThreeSum.LightRadixKeys.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:04.233597+00:00
-- url     : https://prove2.me/submissions/87689ee3-847b-47f3-8a47-35ad51423965

import Definitions.Def_Submission_ThreeSum_LightRadixRows
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Theorems.Thm_ThreeSum_LightRadixKeys_le_offset
import Theorems.Thm_ThreeSum_LightRadixKeys_space_step
import Theorems.Thm_ThreeSum_LightRadixKeys_word_mono
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_Seg_update_out
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Definitions.Def_WeightedCache3SUM_Alias_3f3326597d4f4ccd
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_f8621e0ea40777d9
import Theorems.Thm_ThreeSum_RadixKeyLists_values_length
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixKeys
open Light RadixKeyLists
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightRadixKeys
theorem _root_.solution {pMain pRows pAffine src dst p U : ℕ} (hmain : P[pMain]? = some (body pMain pRows))
    (hrows : P[pRows]? = some (LightRadixRows.body pAffine)) (haffine : P[pAffine]? = some LightReportingAffine.body)
    (base : List ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hsrc : src + base.length ≤ dst) (hm : 0 < base.length)
    (hbound : ∀ x ∈ base, |x| ≤ (U : ℤ)) :
    ∀ J d : ℕ,
      ∀ μ : ℕ → ℤ,
        space dst base.length J ≤ lim.space →
          (word p U J : ℤ) ≤ lim.word →
            d + J + 2 ≤ lim.depth →
              Seg μ src base →
                Meets lim P pMain d [src, base.length, J, p, dst] μ (time base.length J)
                  (fun r ν =>
                    r = ((dst + offset base.length J : ℕ) : ℤ) ∧
                      ν (dst + offset base.length J) = ((base.length ^ J : ℕ) : ℤ) ∧
                        Seg ν (dst + offset base.length J + 1) (values (p : ℤ) base J) ∧ Kept μ ν dst) :=
  by
  intro J
  induction J with
  | zero =>
    intro d μ hspace hword hd hread
    have hs : dst + 2 ≤ lim.space :=
      by
      simp only [space, offset, pow_zero, Nat.add_zero] at hspace
      omega
    apply Meets.of_body hmain
    unfold body time
    refine Ends.iteLast (fun h => False.elim (by simpa using h)) (fun _ => ?_)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen dst (1 : ℕ) ?_ ?_ ?_
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
      refine _root_.Light.Ends.storeToThen (dst + 1) (0 : ℕ) ?_ ?_ ?_
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
      refine _root_.Light.Ends.setToThen (dst : ℕ) ?_ ?_ ?_
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
    refine ⟨by simp [offset], ?_, ?_, ?_⟩
    · simp [offset, Function.update_of_ne (by omega : dst ≠ dst + 1)]
    · simp [values, offset, seg_cons]
    · intro a ha
      simp only [State.mem]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  | succ J ih =>
    intro d μ hspace hword hd hread
    let old := dst + offset base.length J
    let next := old + 1 + base.length ^ J
    have hnext : next = dst + offset base.length (J + 1) := by dsimp [next, old, offset]; omega
    have hs : next + 1 + base.length ^ (J + 1) ≤ lim.space := by rw [hnext]; exact hspace
    have hJ : J + 1 ≤ offset base.length (J + 1) := le_offset _ _
    have hn : 0 < base.length ^ J := Nat.pow_pos hm
    have hrowWord : (LightRadixRows.word p U (U * (p + 1) ^ J) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (word_mono (p := p) (U := U) (Nat.le_succ J))).trans hword
    have hpWord : (p : ℤ) ≤ lim.word := by
      exact (Int.ofNat_le.mpr (show p ≤ word p U (J + 1) by unfold word LightRadixRows.word; omega)).trans hword
    have hprod : (base.length : ℤ) * ((base.length ^ J : ℕ) : ℤ) ≤ lim.word :=
      by
      have hh : base.length * base.length ^ J ≤ lim.space := by rw [← pow_succ']; omega
      exact (by exact_mod_cast hh : (base.length : ℤ) * ((base.length ^ J : ℕ) : ℤ) ≤ lim.space).trans hw
    apply Meets.of_body hmain
    unfold body time
    refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simp at h))
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
            ((ih (d + 1) μ ((space_step dst base.length J).trans hspace) hrowWord (by omega) hread) _ (by omega)) ?_ ?_
            ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen
            (ih (d + 1) μ ((space_step dst base.length J).trans hspace) hrowWord (by omega) hread) ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightRadixRows.time,
              LightReportingAffine.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightRadixRows.time, LightReportingAffine.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightRadixRows.time,
              LightReportingAffine.time] <;>
            omega)
      on_goal -1 =>
        (rintro r ν₀ ⟨hresult, hheader, hprev, hkeep₀⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hr : r = (old : ℤ) := hresult
    have hh : ν₀ old = ((base.length ^ J : ℕ) : ℤ) := hheader
    have hpowerNonneg : (0 : ℤ) ≤ (base.length : ℤ) ^ J := by positivity
    have hprodInt : (base.length : ℤ) * (base.length : ℤ) ^ J ≤ lim.word := by simpa only [Nat.cast_pow] using hprod
    have hprodNonneg : (0 : ℤ) ≤ (base.length : ℤ) * (base.length : ℤ) ^ J := by positivity
    have hnextWord : (old : ℤ) + 1 + (base.length : ℤ) ^ J ≤ lim.word :=
      by
      have hnat : next ≤ lim.space := by omega
      simpa only [next, Nat.cast_add, Nat.cast_one, Nat.cast_pow] using (Int.ofNat_le.mpr hnat).trans hw
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (base.length ^ J : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr, hh,
              LightRadixRows.time, LightReportingAffine.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hr, hh, LightRadixRows.time, LightReportingAffine.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr, hh, LightRadixRows.time,
              LightReportingAffine.time] <;>
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
      refine _root_.Light.Ends.setToThen (next : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr, hh, next,
              LightRadixRows.time, LightReportingAffine.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hr, hh, next, LightRadixRows.time, LightReportingAffine.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr, hh, next, LightRadixRows.time,
              LightReportingAffine.time] <;>
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
      refine _root_.Light.Ends.storeToThen next (base.length ^ (J + 1) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, pow_succ',
              LightRadixRows.time, LightReportingAffine.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [pow_succ', LightRadixRows.time, LightReportingAffine.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, pow_succ', LightRadixRows.time,
              LightReportingAffine.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    let ν₁ := Function.update ν₀ next ((base.length ^ (J + 1) : ℕ) : ℤ)
    have hprev₁ : Seg ν₁ (old + 1) (values (p : ℤ) base J) :=
      by
      apply hprev.update_out
      right
      rw [values_length]
    have hbase₁ : Seg ν₁ src base := by
      intro i hi
      change Function.update ν₀ next _ (src + i) = _
      rw [Function.update_of_ne (by dsimp [next, old]; omega), hkeep₀ _ (by omega)]
      exact hread i hi
    have hsRows : next + 1 + base.length * (values (p : ℤ) base J).length ≤ lim.space :=
      by
      rw [values_length, ← pow_succ']
      exact hs
    have hc :=
      LightRadixRows.meets (d := d + 1) (μ := ν₁) (srcBase := src) (srcPrev := old + 1) (dst := next + 1) (p := p) (U :=
        U) (V := U * (p + 1) ^ J) hrows haffine base (values (p : ℤ) base J) hw (by dsimp [next, old]; omega)
        (by rw [values_length]; dsimp [next]; omega) hsRows hrowWord (by omega) hbase₁ hprev₁ hbound
        (values_bounded p U base hbound J)
    simp only [values_length] at hc
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
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, values_length, hr,
              LightRadixRows.time, LightReportingAffine.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [values_length, hr, LightRadixRows.time, LightReportingAffine.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, values_length, hr, LightRadixRows.time,
              LightReportingAffine.time] <;>
            omega)
      on_goal -1 => (rintro result ν₂ ⟨hvalues, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (next : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightRadixRows.time,
              LightReportingAffine.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightRadixRows.time, LightReportingAffine.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightRadixRows.time,
              LightReportingAffine.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp [hnext], ?_, ?_, ?_⟩
    · change ν₂ (dst + offset base.length (J + 1)) = _
      rw [← hnext, hkeep₁ _ (Or.inl (by omega))]
      exact Function.update_self ..
    · change Seg ν₂ (dst + offset base.length (J + 1) + 1) _
      rw [← hnext]
      exact hvalues
    · intro a ha
      change ν₂ a = μ a
      rw [hkeep₁ _ (Or.inl (by dsimp [next, old]; omega))]
      change Function.update ν₀ next _ a = μ a
      rw [Function.update_of_ne (by dsimp [next, old]; omega)]
      exact hkeep₀ a ha
end ThreeSum.LightRadixKeys
