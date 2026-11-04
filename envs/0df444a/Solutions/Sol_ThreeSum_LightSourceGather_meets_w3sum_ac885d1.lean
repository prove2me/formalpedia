-- Prove2me | solution 1 for ThreeSum.LightSourceGather.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:52:03.863205+00:00
-- url     : https://prove2.me/submissions/b46975f0-3e31-4946-a429-9121802c740a

import Definitions.Def_Submission_ThreeSum_BlockSourceEncoding
import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_6850731862e76136
import Theorems.Thm_Light_frame_append_zeros
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
import Theorems.Thm_ThreeSum_BlockIndexedQuery_prefixIndices_card
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
import Theorems.Thm_ThreeSum_BlockSourceEncoding_modulus_cast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightResidues_emodTime_le
import Theorems.Thm_ThreeSum_LightResidues_residue_cast
import Theorems.Thm_ThreeSum_LightResidues_residue_lt
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_SubsetStages_mem_suffix
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_all
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_zero
import Theorems.Thm_ThreeSum_SubsetStages_suffix_all
import Theorems.Thm_ThreeSum_SubsetStages_suffix_zero
import Theorems.Thm_ThreeSum_SubsetTransport_reindex_map
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
attribute [local simp] ThreeSum.BlockIndexedQuery.prefixIndices_card
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
attribute [local simp] ThreeSum.BlockSourceEncoding.modulus_cast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetStages.mem_suffix
attribute [local simp] ThreeSum.SubsetStages.stageValue_all
attribute [local simp] ThreeSum.SubsetStages.stageValue_zero
attribute [local simp] ThreeSum.SubsetStages.suffix_all
attribute [local simp] ThreeSum.SubsetStages.suffix_zero
attribute [local simp] ThreeSum.SubsetTransport.reindex_map
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceGather
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceGather
theorem _root_.solution {pMain pEmod : ℕ} (hmain : P[pMain]? = some (body pEmod)) (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {raw flags table dst n m work U B : ℕ} (endpoint : ℕ → ℤ) (flag hist : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hm : 0 < m) (hraw : raw + n ≤ dst)
    (hflags : flags + n ≤ dst) (htable : table + m ≤ dst) (hdst : dst + n ≤ work)
    (hspace : work + (Nat.log 2 (U + 1) + 2) ≤ lim.space) (hword : (4 * U + 4 * m + 16 : ℤ) ≤ lim.word)
    (hcountWord : (B : ℤ) ≤ lim.word) (hrawRead : ∀ i < n, μ (raw + i) = endpoint i)
    (hrawBound : ∀ i < n, |endpoint i| ≤ (U : ℤ)) (hflagRead : ∀ i < n, μ (flags + i) = (flag i : ℤ))
    (hflagBound : ∀ i < n, flag i ≤ 1) (hhistRead : ∀ r < m, μ (table + r) = (hist r : ℤ))
    (hhistBound : ∀ r < m, hist r ≤ B) :
    Meets lim P pMain d [raw, flags, table, dst, n, m, work] μ (time n U)
      (fun _ ν => (∀ i < n, ν (dst + i) = (value m endpoint flag hist i : ℤ)) ∧ KeptBut μ ν work dst n) :=
  by
  have hpre : Emod.Pre lim m U work := ⟨hm, hw, hword, hspace⟩
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.for (Inv μ raw flags table dst n m work endpoint flag hist) n (LightResidues.residueBudget U + 72) ?start
      ?round ?done ?bound
  case start =>
    refine ⟨0, μ, ?_, ?_, fun _ _ => rfl⟩
    · exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro j hj; omega
  case round =>
    rintro i _ hi _ ⟨r, ν, rfl, written, kept⟩
    have hread : ν (raw + i) = endpoint i := (kept _ ⟨by omega, Or.inl (by omega)⟩).trans (hrawRead i hi)
    have hx := hrawBound i hi
    have hx' := abs_le.mp hx
    have hbudget := LightResidues.emodTime_le (p := m) hx
    unfold emodTime LightResidues.residueBudget at hbudget
    have hlog : Nat.log 2 (1 + U) = Nat.log 2 (U + 1) := by rw [Nat.add_comm]
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
      | refine _root_.Light.Ends.callToThen ((emod_meets (x := endpoint i) hem hpre hx) _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen (emod_meets (x := endpoint i) hem hpre hx) ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hread,
              LightResidues.residueBudget]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hread, LightResidues.residueBudget] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread, LightResidues.residueBudget] <;> omega)
      on_goal -1 => (rintro q ν₁ ⟨hresult, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hcast := LightResidues.residue_cast hm 1 (endpoint i)
    simp only [one_mul] at hcast
    rw [← hcast] at hresult
    subst q
    have hkeyLt := LightResidues.residue_lt hm 1 (endpoint i)
    have hflag : ν₁ (flags + i) = (flag i : ℤ) :=
      (hkeep _ (by omega)).trans ((kept _ ⟨by omega, Or.inl (by omega)⟩).trans (hflagRead i hi))
    have hflagB := hflagBound i hi
    have hhist :
      ν₁ (table + LightResidues.residue m 1 (endpoint i)) = (hist (LightResidues.residue m 1 (endpoint i)) : ℤ) :=
      (hkeep _ (by omega)).trans ((kept _ ⟨by omega, Or.inl (by omega)⟩).trans (hhistRead _ hkeyLt))
    have hvalue : (hist (LightResidues.residue m 1 (endpoint i)) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (hhistBound _ hkeyLt)).trans hcountWord
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.iteIffThen ((flag i : ℤ) = 1) (fun hy => ?_) (fun hn => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hflag,
              LightResidues.residueBudget]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hflag, LightResidues.residueBudget] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hflag, LightResidues.residueBudget] <;> omega)
      all_goals
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
    · have he : flag i = 1 := by exact_mod_cast hy
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        refine _root_.Light.Ends.storeToThen (dst + i) (hist (LightResidues.residue m 1 (endpoint i)) : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hhist,
                LightResidues.residueBudget]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [hhist, LightResidues.residueBudget] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hhist, LightResidues.residueBudget] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      refine
        ⟨by simp, (LightResidues.residue m 1 (endpoint i) : ℤ),
          Function.update ν₁ (dst + i) (hist (LightResidues.residue m 1 (endpoint i)) : ℕ), by
          simp [update_frame_setLocal], ?_, ?_⟩
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [Function.update_of_ne (by omega)]
          exact (hkeep _ (by omega)).trans (written j hj)
        · simp [value, he]
      · intro a ⟨ha, hout⟩
        rw [Function.update_of_ne (by omega)]
        exact (hkeep a ha).trans (kept a ⟨ha, hout⟩)
    · have he : flag i ≠ 1 := by exact_mod_cast hn
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        refine _root_.Light.Ends.storeToThen (dst + i) (0 : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                LightResidues.residueBudget]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [LightResidues.residueBudget] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightResidues.residueBudget] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      refine
        ⟨by simp, (LightResidues.residue m 1 (endpoint i) : ℤ), Function.update ν₁ (dst + i) 0, by
          simp [update_frame_setLocal], ?_, ?_⟩
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [Function.update_of_ne (by omega)]
          exact (hkeep _ (by omega)).trans (written j hj)
        · simp [value, he]
      · intro a ⟨ha, hout⟩
        rw [Function.update_of_ne (by omega)]
        exact (hkeep a ha).trans (kept a ⟨ha, hout⟩)
  case done =>
    rintro _ _ ⟨r, ν, rfl, written, kept⟩
    exact ⟨written, kept⟩
  case bound =>
    rintro i _ _ _ ⟨r, ν, rfl, _, _⟩
    simp
end ThreeSum.LightSourceGather
