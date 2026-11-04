-- Prove2me | solution 1 for ThreeSum.LightTernaryPairedPotential.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:03:54.623944+00:00
-- url     : https://prove2.me/submissions/4c7167ea-9635-4182-b07d-2743d98443d4

import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_term_abs_le
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_prefixSum_abs_le
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_powTable_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_bound_polynomial
import Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_bound_pos
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_prodCircuits
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_sumCircuits
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_meets
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_tensorIndex_lt
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
import Theorems.Thm_ThreeSum_WeightEnumeration_digit_lt
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_prodCircuits
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_sumCircuits
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPotential
open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators
namespace ThreeSum.LightTernaryPairedPotential
theorem _root_.solution (m base Λ colsBase powers : ℕ) (μ : ℕ → ℤ) {lim : Limits} {P : Program}
    {pMain pPowers pRow pDigit pDivide pPoly depth : ℕ} (hmain : P[pMain]? = some (body m pPowers pRow pPoly))
    (hPowers : P[pPowers]? = some powTableBody) (hRow : P[pRow]? = some (LightWeightRow.body pDigit))
    (hDigit : P[pDigit]? = some (LightRadixDigit.body pDivide)) (hDivide : P[pDivide]? = some LightSmallDivide.body)
    (hPoly : P[pPoly]? = some (LightTernaryPairedPolynomial.body m)) (hΛ : 1 ≤ Λ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : depth + 2 < lim.depth) (hTspace : base + Λ ^ 4 ≤ lim.space) (hCspace : colsBase + width m ≤ lim.space)
    (hPspace : powers + (width m + 1) ≤ lim.space) (hTC : Apart base (Λ ^ 4) colsBase (width m))
    (hTP : Apart base (Λ ^ 4) powers (width m + 1)) (hPC : Apart powers (width m + 1) colsBase (width m)) (U : ℤ)
    (hU : 0 ≤ U) (hTabs : ∀ k < Λ ^ 4, |μ (base + k)| ≤ U) (hWord : word m Λ U ≤ lim.word)
    (hPolyWord : (polynomial m).coefficient * (U + 1) ^ (polynomial m).degree ≤ lim.word) :
    Meets lim P pMain depth [base, Λ, colsBase, powers] μ (time m Λ)
      (fun r ν =>
        r = prefixSum m base Λ μ (Λ ^ width m) ∧
          (∀ k < Λ ^ 4, ν (base + k) = μ (base + k)) ∧ Kept μ ν (min colsBase powers)) :=
  by
  let B := (polynomial m).bound U
  let N := Λ ^ width m
  have hwidth : width m = m + m := by simp [width, PairedIndex, Fintype.card_sum]
  have hNp : (0 : ℤ) ≤ (Λ : ℤ) ^ width m := pow_nonneg (Int.natCast_nonneg _) _
  have hNLp : (0 : ℤ) ≤ (Λ : ℤ) ^ (width m + 1) := pow_nonneg (Int.natCast_nonneg _) _
  have hDimNonneg : (0 : ℤ) ≤ width m := Int.natCast_nonneg _
  have hB : 1 ≤ B := (polynomial m).bound_pos hU
  have hwordNat (x : ℕ) (hx : x ≤ Λ ^ (width m + 1) + N + width m + Λ + 2) : (x : ℤ) ≤ lim.word :=
    by
    have hh : (x : ℤ) ≤ Λ ^ (width m + 1) + N + width m + Λ + 2 := by exact_mod_cast hx
    unfold word at hWord
    push_cast at hWord
    dsimp [B, N] at *
    nlinarith [Nat.zero_le (Λ ^ (width m + 1)), Nat.zero_le (Λ ^ width m)]
  have hNWord := hwordNat N (by omega)
  have hdimWord := hwordNat (width m) (by omega)
  have hΛWord := hwordNat Λ (by omega)
  have hOneWord := hwordNat 1 (by omega)
  have hBWord : B ≤ lim.word := ((polynomial m).bound_polynomial hU).trans hPolyWord
  have hsumWord : (N + 1 : ℤ) * B ≤ lim.word := by
    unfold word at hWord
    push_cast at hWord
    dsimp [B, N] at *
    nlinarith [Nat.zero_le (Λ ^ (width m + 1)), Nat.zero_le (Λ ^ width m)]
  apply Meets.of_body hmain
  unfold body time
  have hp :=
    powTable_meets (d := depth + 1) (μ := μ) (dst := powers) (L := width m + 1) (b := Λ) hPowers hw hPspace
      (by
        intro j hj
        exact hwordNat (Λ ^ j) ((Nat.pow_le_pow_right hΛ hj).trans (by omega)))
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWeightRow.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWeightRow.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightRow.time] <;> omega)
    on_goal -1 => (rintro powRet μ₁ ⟨hpow, hpowKeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hpread (e : ℕ) (he : e ≤ width m) : μ₁ (powers + e) = ((Λ ^ e : ℕ) : ℤ) := by
    exact (by simpa [powList] using hpow e (by simp; omega))
  have hTread (k : ℕ) (hk : k < Λ ^ 4) : μ₁ (base + k) = μ (base + k) := by exact hpowKeep _ (by omega)
  have hT₁ (k : ℕ) (hk : k < Λ ^ 4) : |μ₁ (base + k)| ≤ U := by rw [hTread k hk]; exact hTabs k hk
  have hlast := hpread (width m) le_rfl
  simp only [hwidth] at hlast
  have hlastInt : μ₁ ((powers : ℤ) + ((m : ℤ) + m)).toNat = (N : ℤ) :=
    by
    have he : ((powers : ℤ) + ((m : ℤ) + m)).toNat = powers + (m + m) := by omega
    rw [he]
    simpa [N, hwidth] using hlast
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (N : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlastInt, hwidth, N, LightWeightRow.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hlastInt, hwidth, N, LightWeightRow.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlastInt, hwidth, N, LightWeightRow.time] <;>
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
    refine _root_.Light.Ends.setToThen (0 : ℤ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWeightRow.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWeightRow.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightRow.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.pieceThen
      (Ends.for (T := N * (LightWeightRow.time (width m) N + LightTernaryPairedPolynomial.time m + 250) + 20) (Q :=
        Inv m base Λ colsBase powers μ₁ powRet N) (Inv m base Λ colsBase powers μ₁ powRet) N
        (LightWeightRow.time (width m) N + LightTernaryPairedPolynomial.time m + 240) ?_ ?_ ?_ ?_ (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, N, hwidth]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [N, hwidth] <;>
              first
              | omega
              | (ring_nf; omega))))
      ?_ (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, N, hwidth]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [N, hwidth] <;>
            first
            | omega
            | (ring_nf; omega)))
  · refine ⟨0, 0, μ₁, ?_, SameOutside.refl⟩
    simp [Inv, prefixSum, update_frame_setLocal, N]
    exact (frame_append_zeros ([base, Λ, colsBase, powers, powRet, ((Λ ^ (m + m) : ℕ) : ℤ), 0, 0] : List ℤ) 2).symm
  · rintro i _ hi _ ⟨r₀, r₁, ν, rfl, hkeep⟩
    have hpowν (e : ℕ) (he : e ≤ width m) : ν (powers + e) = ((Λ ^ e : ℕ) : ℤ) :=
      by
      rw [hkeep _ (by omega)]
      exact hpread e he
    have hreadν (k : ℕ) (hk : k < Λ ^ 4) : ν (base + k) = μ₁ (base + k) := hkeep _ (by omega)
    have hRowWord : (LightWeightRow.word (width m) Λ i 0 1 : ℤ) ≤ lim.word :=
      by
      have hx : LightWeightRow.word (width m) Λ i 0 1 ≤ 4 * (Λ ^ (width m + 1) + N + width m + Λ + 2) := by
        unfold LightWeightRow.word; omega
      have hz := Int.ofNat_le.mpr hx
      unfold word at hWord
      push_cast at hWord hz
      dsimp [N, B] at *
      nlinarith
    have hrow :=
      LightWeightRow.meets (d := depth + 1) (μ := ν) (W := width m) (p := Λ) (k := i) (powers := powers) (start := 0)
        (stride := 1) (dst := colsBase) (n := width m) hRow hDigit hDivide hw (by omega) hΛ hCspace hPspace hPC hRowWord
        (by intro j hj; omega) hpowν
    have hrowTime : LightWeightRow.time (width m) i ≤ LightWeightRow.time (width m) N :=
      by
      unfold LightWeightRow.time LightRadixDigit.time
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
    have hNcanonical : N = Λ ^ (m * 2) := by simp only [N, hwidth]; congr 1; omega
    have hmi : m * i ≤ m * (Λ ^ (m * 2)) := Nat.mul_le_mul_left m (by omega)
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
      | refine _root_.Light.Ends.callToThen (hrow _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hrow ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, width, N,
              LightWeightRow.time, LightRadixDigit.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [width, N, LightWeightRow.time, LightRadixDigit.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, width, N, LightWeightRow.time,
              LightRadixDigit.time] <;>
            omega)
      on_goal -1 => (rintro rowRet ν₁ ⟨hcols, hrowKeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hkeep₁ := hkeep.trans hrowKeep
    have hread₁ (k : ℕ) (hk : k < Λ ^ 4) : ν₁ (base + k) = μ₁ (base + k) := hkeep₁ _ (by omega)
    have hcolsr (r : PairedIndex m) :
      ν₁ (colsBase + (Fintype.equivFin (PairedIndex m) r).val) = (columns m Λ i r : ℤ) := by
      simpa [columns] using hcols _ (Fintype.equivFin (PairedIndex m) r).isLt
    have hpoly :=
      LightTernaryPairedPolynomial.meets m base Λ colsBase (columns m Λ i) ν₁ (depth := depth + 1) hPoly hΛ
        (fun r => WeightEnumeration.digit_lt (by omega)) hcolsr hTspace hCspace hw U hU
        (by intro k hk; rw [hread₁ k hk]; exact hT₁ k hk) hPolyWord
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
      | refine _root_.Light.Ends.callToThen (hpoly _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hpoly ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, width, N,
              LightWeightRow.time, LightRadixDigit.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [width, N, LightWeightRow.time, LightRadixDigit.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, width, N, LightWeightRow.time,
              LightRadixDigit.time] <;>
            omega)
      on_goal -1 => (rintro result ν₂ ⟨hresult, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ν₂
    have heval : result = term m base Λ μ₁ i := by
      rw [hresult]
      unfold term
      congr 1
      funext q
      exact
        hread₁ _
          (tensorIndex_lt (WeightEnumeration.digit_lt (by omega)) (WeightEnumeration.digit_lt (by omega))
            (WeightEnumeration.digit_lt (by omega)) (WeightEnumeration.digit_lt (by omega)))
    have hacc := prefixSum_abs_le m base Λ μ₁ U hU hΛ hT₁ i
    have hterm := term_abs_le m base Λ μ₁ U hU hΛ hT₁ i
    have haccWord : |prefixSum m base Λ μ₁ i| ≤ lim.word :=
      by
      have hh : (i : ℤ) * B ≤ (N + 1 : ℤ) * B :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : i ≤ N + 1)) (by omega)
      exact hacc.trans (hh.trans hsumWord)
    have htermWord := hterm.trans hBWord
    have ⟨haccLo, haccHi⟩ := abs_le.mp haccWord
    have ⟨htermLo, htermHi⟩ := abs_le.mp htermWord
    have hnext := prefixSum_abs_le m base Λ μ₁ U hU hΛ hT₁ (i + 1)
    have hnextWord : |prefixSum m base Λ μ₁ (i + 1)| ≤ lim.word :=
      by
      have hh : ((i + 1 : ℕ) : ℤ) * B ≤ (N + 1 : ℤ) * B :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : i + 1 ≤ N + 1)) (by omega)
      exact hnext.trans (hh.trans hsumWord)
    have hprefixSum : prefixSum m base Λ μ₁ (i + 1) = prefixSum m base Λ μ₁ i + term m base Λ μ₁ i :=
      Finset.sum_range_succ _ _
    have ⟨hnextLo, hnextHi⟩ := abs_le.mp hnextWord
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (prefixSum m base Λ μ₁ (i + 1)) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, heval, hprefixSum,
              width, N, LightWeightRow.time, LightRadixDigit.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [heval, hprefixSum, width, N, LightWeightRow.time, LightRadixDigit.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, heval, hprefixSum, width, N,
              LightWeightRow.time, LightRadixDigit.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp, rowRet, result, ν₁, ?_, hkeep₁⟩
    simp [Inv, update_frame_setLocal]
  · intro σ hcounter hshape
    exact hshape
  · rintro i _ hi _ ⟨r₀, r₁, ν, rfl, hkeep⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, N, hwidth] <;> omega)
  · rintro σ ⟨r₀, r₁, ν, rfl, hkeep⟩
    have hfinalEq : prefixSum m base Λ μ₁ N = prefixSum m base Λ μ N :=
      by
      unfold prefixSum
      apply Finset.sum_congr rfl
      intro i hi
      unfold term
      congr 1
      funext q
      exact
        hTread _
          (tensorIndex_lt (WeightEnumeration.digit_lt (by omega)) (WeightEnumeration.digit_lt (by omega))
            (WeightEnumeration.digit_lt (by omega)) (WeightEnumeration.digit_lt (by omega)))
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (prefixSum m base Λ μ₁ N) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, width, N,
              LightWeightRow.time, LightRadixDigit.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [width, N, LightWeightRow.time, LightRadixDigit.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, width, N, LightWeightRow.time,
              LightRadixDigit.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨hfinalEq, ?_, ?_⟩
    · intro k hk
      exact (hkeep _ (by omega)).trans (hTread k hk)
    · intro x hx
      exact (hkeep x (by omega)).trans (hpowKeep x (by omega))
end ThreeSum.LightTernaryPairedPotential
