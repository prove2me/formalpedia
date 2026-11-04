-- Prove2me | solution 1 for ThreeSum.LightSubsetOffset.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:35:30.907051+00:00
-- url     : https://prove2.me/submissions/9c216162-4621-4006-b223-cff92f496f53

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Theorems.Thm_ThreeSum_LightSubsetOffset_layerOffset_bound
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_setLast
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightSubsetAddress_cell_offset_lt
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_succ
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
open ThreeSum ThreeSum.LightSubsetOffset
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSubsetOffset
theorem _root_.solution {pOffset table W L k : ℕ} (hprog : P[pOffset]? = some body) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : table + tableSize W ≤ lim.space)
    (hword : (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word) (htable : Table μ table W) (hL : L ≤ W) (hk : k ≤ W) :
    Meets lim P pOffset d [table, L, k, W] μ (time k) (fun r μ' => r = (layerOffset L k : ℤ) ∧ μ' = μ) :=
  by
  have hsize : W + 1 ≤ tableSize W := by unfold tableSize; nlinarith
  have hpow : (2 ^ L : ℕ) ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hacc (i : ℕ) (hi : i ≤ k) : (layerOffset L i : ℤ) ≤ lim.word :=
    by
    have hm := Nat.mul_le_mul (show i ≤ W + 1 by omega) hpow
    have hb := (layerOffset_bound L i).trans hm
    have hbZ : (layerOffset L i : ℤ) ≤ (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ) := by exact_mod_cast hb
    exact hbZ.trans hword
  have hcast : (L : ℤ) * ((W : ℤ) + 1) = ((L * (W + 1) : ℕ) : ℤ) := by push_cast; rfl
  apply Meets.of_body hprog
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
    refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
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
      (Ends.for (T := 30 * k + 6) (Q := fun σ => σ = ⟨frame [table, L, k, W, k, (layerOffset L k : ℕ)], μ⟩)
        (fun i σ => σ = ⟨frame [table, L, k, W, i, (layerOffset L i : ℕ)], μ⟩) k 22 ?_ ?_ ?_ ?_ (hT := by
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
              | (ring_nf; omega))))
      ?_
  · simp [update_frame_setLocal]
  · rintro i _ hi _ rfl
    have hiW : i ≤ W := by omega
    have htRead := htable L hL i hiW
    have haddr : table + L * (W + 1) + i < lim.space :=
      by
      have hh := cell_offset_lt hL hiW
      omega
    have haddrEq : ((table : ℤ) + (L : ℤ) * ((W : ℤ) + 1) + (i : ℤ)).toNat = table + L * (W + 1) + i :=
      by
      have he : (table : ℤ) + (L : ℤ) * ((W : ℤ) + 1) + (i : ℤ) = ((table + L * (W + 1) + i : ℕ) : ℤ) := by
        push_cast
        rfl
      rw [he, Int.toNat_natCast]
    have htReadZ : μ (((table : ℤ) + (L : ℤ) * ((W : ℤ) + 1) + (i : ℤ)).toNat) = (L.choose i : ℤ) := by
      rw [haddrEq, htRead]
    have hsum := hacc (i + 1) (by omega)
    rw [layerOffset_succ, Nat.cast_add] at hsum
    have hnonneg : (0 : ℤ) ≤ (layerOffset L i : ℤ) := Int.natCast_nonneg _
    have hcNonneg : (0 : ℤ) ≤ (L.choose i : ℤ) := Int.natCast_nonneg _
    refine
      Ends.setLast ?_ (hs := by
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, htReadZ] <;> omega)) (hT := by
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
              | (ring_nf; omega)))
    simp [update_frame_setLocal, htReadZ, layerOffset_succ]
  · intro σ hc hs
    exact hs
  · rintro i _ hi _ rfl
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  · intro σ hs
    rw [hs]
    have hf := hacc k le_rfl
    have hn : (0 : ℤ) ≤ (layerOffset L k : ℤ) := Int.natCast_nonneg _
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (layerOffset L k : ℕ) ?_ ?_ ?_
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
    exact ⟨rfl, rfl⟩
end ThreeSum.LightSubsetOffset
