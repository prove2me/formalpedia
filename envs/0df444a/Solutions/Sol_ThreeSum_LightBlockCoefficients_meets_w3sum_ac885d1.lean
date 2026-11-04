-- Prove2me | solution 1 for ThreeSum.LightBlockCoefficients.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:30:12.347198+00:00
-- url     : https://prove2.me/submissions/ba57ff38-ccb3-4f53-8a7b-7bd3740620c4

import Definitions.Def_Submission_ThreeSum_LightScaleArray
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_BlockIndex
import Definitions.Def_Submission_ThreeSum_LightBlockCoefficients
import Theorems.Thm_ThreeSum_LightBlockCoefficients_row_end_le
import Theorems.Thm_ThreeSum_LightBlockCoefficients_map_end_le
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
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_BlockEncoding_leftSubset_fromSubsets
import Theorems.Thm_ThreeSum_BlockEncoding_rightSubset_fromSubsets
import Theorems.Thm_ThreeSum_BlockEncoding_row_leftSubset
import Theorems.Thm_ThreeSum_BlockEncoding_row_outputSubset
import Theorems.Thm_ThreeSum_BlockEncoding_row_rightSubset
import Theorems.Thm_ThreeSum_BlockIndex_coordEquiv_val
import Theorems.Thm_ThreeSum_BlockIndex_indexSet_card
import Theorems.Thm_ThreeSum_BlockIndex_indexSet_subset
import Theorems.Thm_ThreeSum_BlockIndex_indexSet_union
import Theorems.Thm_ThreeSum_BlockIndex_index_unindex
import Theorems.Thm_ThreeSum_BlockIndex_mem_indexSet
import Theorems.Thm_ThreeSum_BlockIndex_unindex_index
import Theorems.Thm_ThreeSum_BlockRows_flat_row
import Theorems.Thm_ThreeSum_BlockRows_mem_flat
import Theorems.Thm_ThreeSum_BlockRows_mem_join
import Theorems.Thm_ThreeSum_BlockRows_mem_prefixIndices
import Theorems.Thm_ThreeSum_BlockRows_mem_row
import Theorems.Thm_ThreeSum_BlockRows_row_flat
import Theorems.Thm_ThreeSum_BlockRows_row_inter
import Theorems.Thm_ThreeSum_BlockRows_row_join
import Theorems.Thm_ThreeSum_BlockRows_row_sdiff
import Theorems.Thm_ThreeSum_BlockRows_row_union
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightScaleArray_meets
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
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.BlockEncoding.leftSubset_fromSubsets
attribute [local simp] ThreeSum.BlockEncoding.rightSubset_fromSubsets
attribute [local simp] ThreeSum.BlockEncoding.row_leftSubset
attribute [local simp] ThreeSum.BlockEncoding.row_outputSubset
attribute [local simp] ThreeSum.BlockEncoding.row_rightSubset
attribute [local simp] ThreeSum.BlockIndex.coordEquiv_val
attribute [local simp] ThreeSum.BlockIndex.indexSet_card
attribute [local simp] ThreeSum.BlockIndex.indexSet_subset
attribute [local simp] ThreeSum.BlockIndex.indexSet_union
attribute [local simp] ThreeSum.BlockIndex.index_unindex
attribute [local simp] ThreeSum.BlockIndex.mem_indexSet
attribute [local simp] ThreeSum.BlockIndex.unindex_index
attribute [local simp] ThreeSum.BlockRows.flat_row
attribute [local simp] ThreeSum.BlockRows.mem_flat
attribute [local simp] ThreeSum.BlockRows.mem_join
attribute [local simp] ThreeSum.BlockRows.mem_prefixIndices
attribute [local simp] ThreeSum.BlockRows.mem_row
attribute [local simp] ThreeSum.BlockRows.row_flat
attribute [local simp] ThreeSum.BlockRows.row_inter
attribute [local simp] ThreeSum.BlockRows.row_join
attribute [local simp] ThreeSum.BlockRows.row_sdiff
attribute [local simp] ThreeSum.BlockRows.row_union
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockCoefficients
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBlockCoefficients
theorem _root_.solution {pMain pPowers pScale : ℕ} (hmain : P[pMain]? = some (body pPowers pScale))
    (hpowers : P[pPowers]? = some powTableBody) (hscale : P[pScale]? = some LightScaleArray.body) {μ : ℕ → ℤ}
    {J L p occ maps dst0 dst1 work U M d : ℕ} (sel : ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hp : 1 ≤ p) (hocc : occ + J ≤ dst0) (hmaps : maps + 2 * L * M ≤ dst0) (hdst0 : dst0 + J * L ≤ dst1)
    (hdst1 : dst1 + J * L ≤ work) (hspace : work + (J + 1) ≤ lim.space) (hword : (word J p U : ℤ) ≤ lim.word)
    (hd : d < lim.depth) (hsel : ∀ j < J, sel j < M) (hselRead : ∀ j < J, μ (occ + j) = (sel j : ℤ))
    (hread0 : ∀ s < M, ∀ i < L, μ (maps + 2 * L * s + i) = (w0 s i : ℤ))
    (hread1 : ∀ s < M, ∀ i < L, μ (maps + 2 * L * s + L + i) = (w1 s i : ℤ)) (hbound0 : ∀ s < M, ∀ i < L, w0 s i ≤ U)
    (hbound1 : ∀ s < M, ∀ i < L, w1 s i ≤ U) :
    Meets lim P pMain d [J, L, p, occ, maps, dst0, dst1, work] μ (time J L)
      (fun _ ν => Rows ν dst0 dst1 L p sel w0 w1 J ∧ Kept μ ν dst0 ∧ Powers ν work J p) :=
  by
  have hpw : ∀ i ≤ J + 1, ((p ^ i : ℕ) : ℤ) ≤ lim.word :=
    by
    intro i hi
    have hh : p ^ i ≤ word J p U := (Nat.pow_le_pow_right hp hi).trans (Nat.le_mul_of_pos_right _ (by omega))
    exact (by exact_mod_cast hh : ((p ^ i : ℕ) : ℤ) ≤ (word J p U : ℤ)).trans hword
  have hpb : (p : ℤ) ≤ lim.word := by simpa using hpw 1 (by omega)
  apply Meets.of_body hmain
  unfold body time
  have hpCall := powTable_meets (d := d + 1) (μ := μ) (dst := work) (L := J + 1) (b := p) hpowers hw hspace hpw
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
    | refine _root_.Light.Ends.callToThen (hpCall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hpCall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime, roundTime,
            LightScaleArray.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, roundTime, LightScaleArray.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime, roundTime,
            LightScaleArray.time] <;>
          omega)
    on_goal -1 => (rintro rPow ν₀ ⟨hpow, hkeep₀⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine
    Ends.for (Inv μ J L p occ maps dst0 dst1 work sel w0 w1) J (roundTime L) ?start ?round ?done ?bound (hT := by
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
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, 0, 0, 0, 0, ν₀, ?_, ?_, ?_, ?_⟩
    · simp [update_frame_setLocal]
      change
        frame [(J : ℤ), L, p, occ, maps, dst0, dst1, work, 0] =
          frame ([(J : ℤ), L, p, occ, maps, dst0, dst1, work, 0] ++ [0, 0, 0, 0, 0])
      exact (frame_append_zeros _ 5).symm
    · intro a ha
      omega
    · intro a ha
      exact hkeep₀ a (Or.inl (by omega))
    · intro i hi
      have hh := hpow i (by simp; omega)
      simpa only [getElem_powList] using hh
  case round =>
    rintro j _ hj _ ⟨s, a, b, r0, r1, ν, rfl, hrows, hkept, hpows⟩
    have hs := hsel j hj
    have hme := map_end_le (L := L) hs
    have hre := row_end_le (L := L) hj
    have htwo : 2 * L ≤ lim.space := (Nat.le_mul_of_pos_right (2 * L) (by omega : 0 < M)).trans (by omega)
    have hprod : 2 * (L : ℤ) * (sel j : ℤ) ≤ lim.word :=
      by
      have hh : 2 * L * sel j ≤ lim.space := by omega
      exact (by exact_mod_cast hh : 2 * (L : ℤ) * (sel j : ℤ) ≤ lim.space).trans hw
    have hprodNonneg : 0 ≤ 2 * (L : ℤ) * (sel j : ℤ) := by positivity
    have haddrWord : (maps : ℤ) + 2 * (L : ℤ) * (sel j : ℤ) ≤ lim.word :=
      by
      have hh : maps + 2 * L * sel j ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (maps : ℤ) + 2 * (L : ℤ) * (sel j : ℤ) ≤ lim.space).trans hw
    have haddrEndWord : (maps : ℤ) + 2 * (L : ℤ) * (sel j : ℤ) + (L : ℤ) + (L : ℤ) ≤ lim.word :=
      by
      have hh : maps + 2 * L * sel j + L + L ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (maps : ℤ) + 2 * (L : ℤ) * (sel j : ℤ) + (L : ℤ) + (L : ℤ) ≤ lim.space).trans hw
    have hrowProd : (j : ℤ) * (L : ℤ) ≤ lim.word :=
      by
      have hh : j * L ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (j : ℤ) * (L : ℤ) ≤ lim.space).trans hw
    have hrowNonneg : 0 ≤ (j : ℤ) * (L : ℤ) := by positivity
    have hselection : ν (occ + j) = (sel j : ℤ) := (hkept _ (by omega)).trans (hselRead j hj)
    have hpower := hpows j (by omega)
    have hread0' : ∀ i < L, ν (maps + 2 * L * sel j + i) = (w0 (sel j) i : ℤ) :=
      by
      intro i hi
      exact (hkept _ (by omega)).trans (hread0 _ hs i hi)
    have hread1' : ∀ i < L, ν (maps + 2 * L * sel j + L + i) = (w1 (sel j) i : ℤ) :=
      by
      intro i hi
      exact (hkept _ (by omega)).trans (hread1 _ hs i hi)
    have hv0 : ∀ i < L, |(p ^ j : ℕ) * ν (maps + 2 * L * sel j + i)| ≤ lim.word :=
      by
      intro i hi
      rw [hread0' i hi]
      have hh : p ^ j * w0 (sel j) i ≤ word J p U :=
        Nat.mul_le_mul (Nat.pow_le_pow_right hp (by omega)) ((hbound0 _ hs i hi).trans (Nat.le_succ U))
      have hz : (((p ^ j * w0 (sel j) i : ℕ) : ℤ)) ≤ lim.word :=
        (by exact_mod_cast hh : ((p ^ j * w0 (sel j) i : ℕ) : ℤ) ≤ (word J p U : ℤ)).trans hword
      simpa only [Nat.cast_mul, abs_mul, abs_of_nonneg (Int.natCast_nonneg _), Int.abs_natCast] using hz
    unfold roundBody roundTime
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (maps + 2 * L * sel j : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hselection,
              LightScaleArray.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hselection, LightScaleArray.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hselection, LightScaleArray.time] <;> omega)
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
      refine _root_.Light.Ends.setToThen (dst0 + j * L : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightScaleArray.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightScaleArray.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightScaleArray.time] <;> omega)
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
      refine _root_.Light.Ends.setToThen (dst1 + j * L : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightScaleArray.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightScaleArray.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightScaleArray.time] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    have hcall0 :=
      LightScaleArray.meets (d := d + 1) (src := maps + 2 * L * sel j) (dst := dst0 + j * L) (n := L) (c := (p ^ j : ℕ))
        hscale hw (by omega) (by omega) (Or.inr (Or.inl (by omega))) hv0
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
      | refine _root_.Light.Ends.callToThen (hcall0 _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hcall0 ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hpower,
              LightScaleArray.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hpower, LightScaleArray.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hpower, LightScaleArray.time] <;> omega)
      on_goal -1 => (rintro q0 ν₁ ⟨hout0, hkeep0⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hpower₁ : ν₁ (work + j) = ((p ^ j : ℕ) : ℤ) := (hkeep0 _ (Or.inr (by omega))).trans hpower
    have hread1'' : ∀ i < L, ν₁ (maps + 2 * L * sel j + L + i) = (w1 (sel j) i : ℤ) :=
      by
      intro i hi
      exact (hkeep0 _ (Or.inl (by omega))).trans (hread1' i hi)
    have hv1 : ∀ i < L, |(p ^ j : ℕ) * ν₁ (maps + 2 * L * sel j + L + i)| ≤ lim.word :=
      by
      intro i hi
      rw [hread1'' i hi]
      have hh : p ^ j * w1 (sel j) i ≤ word J p U :=
        Nat.mul_le_mul (Nat.pow_le_pow_right hp (by omega)) ((hbound1 _ hs i hi).trans (Nat.le_succ U))
      have hz : (((p ^ j * w1 (sel j) i : ℕ) : ℤ)) ≤ lim.word :=
        (by exact_mod_cast hh : ((p ^ j * w1 (sel j) i : ℕ) : ℤ) ≤ (word J p U : ℤ)).trans hword
      simpa only [Nat.cast_mul, abs_mul, abs_of_nonneg (Int.natCast_nonneg _), Int.abs_natCast] using hz
    have hcall1 :=
      LightScaleArray.meets (d := d + 1) (src := maps + 2 * L * sel j + L) (dst := dst1 + j * L) (n := L) (c :=
        (p ^ j : ℕ)) hscale hw (by omega) (by omega) (Or.inr (Or.inl (by omega))) hv1
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
      | refine _root_.Light.Ends.callToThen (hcall1 _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hcall1 ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hpower₁,
              LightScaleArray.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hpower₁, LightScaleArray.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hpower₁, LightScaleArray.time] <;> omega)
      on_goal -1 => (rintro q1 ν₂ ⟨hout1, hkeep1⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine
      ⟨by simp, ((maps + 2 * L * sel j : ℕ) : ℤ), ((dst0 + j * L : ℕ) : ℤ), ((dst1 + j * L : ℕ) : ℤ), q0, q1, ν₂, ?_,
        ?_, ?_, ?_⟩
    · simp [update_frame_setLocal]
    · intro a ha i hi
      by_cases haj : a = j
      · subst a
        constructor
        · rw [hkeep1 _ (Or.inl (by omega)), hout0 i hi, hread0' i hi, Nat.cast_mul]
        · simpa only [Nat.cast_mul] using (hout1 i hi).trans (by rw [hread1'' i hi])
      · have hal : a < j := by omega
        have he : a * L + i < j * L := by
          have hh := row_end_le (L := L) hal
          omega
        constructor
        · exact (hkeep1 _ (Or.inl (by omega))).trans ((hkeep0 _ (Or.inl (by omega))).trans (hrows a hal i hi).1)
        · exact (hkeep1 _ (Or.inl (by omega))).trans ((hkeep0 _ (Or.inr (by omega))).trans (hrows a hal i hi).2)
    · intro a ha
      exact (hkeep1 _ (Or.inl (by omega))).trans ((hkeep0 _ (Or.inl (by omega))).trans (hkept a ha))
    · intro a ha
      exact (hkeep1 _ (Or.inr (by omega))).trans ((hkeep0 _ (Or.inr (by omega))).trans (hpows a ha))
  case done =>
    rintro _ _ ⟨s, a, b, r0, r1, ν, rfl, hrows, hkept, hpows⟩
    exact ⟨hrows, hkept, hpows⟩
  case bound =>
    rintro j _ hj _ ⟨s, a, b, r0, r1, ν, rfl, _, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightBlockCoefficients
