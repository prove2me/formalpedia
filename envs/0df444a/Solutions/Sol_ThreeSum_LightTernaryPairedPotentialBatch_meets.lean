-- Prove2me | solution 1 for ThreeSum.LightTernaryPairedPotentialBatch.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:13:55.733212+00:00
-- url     : https://prove2.me/submissions/e89ad311-6a71-41ad-8e96-627dce1297a8

import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotentialBatch
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_List_abs_sum_le_sum_abs
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_bound_pos
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_prodCircuits
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_sumCircuits
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_meets
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_tensorIndex_lt
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_meets
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_prefixSum_abs_le
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_digit
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_divide
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_main
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_polynomial
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_powers
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_row
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
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_digit
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_divide
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_main
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_polynomial
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_powers
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_row
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
open ThreeSum ThreeSum.LightTernaryPairedPotentialBatch
open Light LightTernaryPairedPotential
open scoped BigOperators
set_option maxHeartbeats 2000000
namespace ThreeSum.LightTernaryPairedPotentialBatch
theorem _root_.solution {lim : Limits} {P : Program} {pMain pPotential pPowers pRow pDigit pDivide pPoly d : ℕ}
    (K base Λ H cols powers cutoff : ℕ) (μ : ℕ → ℤ) (hmain : P[pMain]? = some (body pPotential))
    (hPotential : P[pPotential]? = some (LightTernaryPairedPotential.body K pPowers pRow pPoly))
    (hPowers : P[pPowers]? = some powTableBody) (hRow : P[pRow]? = some (LightWeightRow.body pDigit))
    (hDigit : P[pDigit]? = some (LightRadixDigit.body pDivide)) (hDivide : P[pDivide]? = some LightSmallDivide.body)
    (hPoly : P[pPoly]? = some (LightTernaryPairedPolynomial.body K)) (hΛ : 1 ≤ Λ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 3 < lim.depth) (hcut : base + H * Λ ^ 4 ≤ cutoff) (hcutSpace : cutoff ≤ lim.space)
    (hcols : cols + TernaryPairedColumnEnumeration.width K ≤ lim.space)
    (hpowers : powers + (TernaryPairedColumnEnumeration.width K + 1) ≤ lim.space) (hcutCols : cutoff ≤ cols)
    (hcutPowers : cutoff ≤ powers)
    (hApart : Apart powers (TernaryPairedColumnEnumeration.width K + 1) cols (TernaryPairedColumnEnumeration.width K))
    (U : ℤ) (hU : 0 ≤ U) (hread : ∀ i < H, ∀ q < Λ ^ 4, |μ (base + i * Λ ^ 4 + q)| ≤ U)
    (hKernelWord : LightTernaryPairedPotential.word K Λ U ≤ lim.word)
    (hPolyWord :
      (LightTernaryPairedPolynomial.polynomial K).coefficient *
          (U + 1) ^ (LightTernaryPairedPolynomial.polynomial K).degree ≤
        lim.word)
    (hSumWord :
      (H : ℤ) * (Λ ^ TernaryPairedColumnEnumeration.width K : ℕ) * (LightTernaryPairedPolynomial.polynomial K).bound U ≤
        lim.word)
    (hHword : (H : ℤ) ≤ lim.word) :
    Meets lim P pMain d [base, Λ, H, cols, powers] μ (time K Λ H)
      (fun r ν => r = total K base Λ μ H ∧ Kept μ ν cutoff) :=
  by
  let E : ℤ := (Λ ^ TernaryPairedColumnEnumeration.width K : ℕ) * (LightTernaryPairedPolynomial.polynomial K).bound U
  have hPolyBound : 1 ≤ (LightTernaryPairedPolynomial.polynomial K).bound U :=
    (LightTernaryPairedPolynomial.polynomial K).bound_pos hU
  have hE : 0 ≤ E := mul_nonneg (Int.natCast_nonneg _) (by omega)
  have hterm (i : ℕ) (hi : i < H) : |term K base Λ μ i| ≤ E :=
    LightTernaryPairedPotential.prefixSum_abs_le K (base + i * Λ ^ 4) Λ μ U hU hΛ (hread i hi) _
  have htotal (i : ℕ) (hi : i ≤ H) : |total K base Λ μ i| ≤ lim.word :=
    by
    have hh : |total K base Λ μ i| ≤ (i : ℤ) * E := by
      unfold total
      calc
        _ ≤ ∑ j ∈ Finset.range i, |term K base Λ μ j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j ∈ Finset.range i, E :=
          (Finset.sum_le_sum fun j hj => hterm j (by have := Finset.mem_range.mp hj; omega))
        _ = _ := by simp
    have hb : (i : ℤ) * E ≤ (H : ℤ) * E := mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hE
    exact hh.trans (hb.trans (by simpa [E, mul_assoc] using hSumWord))
  have hΛword : (Λ : ℤ) ≤ lim.word :=
    by
    have hp : 0 ≤ LightTernaryPairedPotential.word K Λ U :=
      by
      unfold LightTernaryPairedPotential.word
      have := (LightTernaryPairedPolynomial.polynomial K).bound_pos hU
      positivity
    unfold LightTernaryPairedPotential.word at hKernelWord
    have := (LightTernaryPairedPolynomial.polynomial K).bound_pos hU
    push_cast at hKernelWord
    nlinarith [Nat.zero_le (Λ ^ (TernaryPairedColumnEnumeration.width K + 1)),
      Nat.zero_le (Λ ^ TernaryPairedColumnEnumeration.width K)]
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
    refine _root_.Light.Ends.setToThen (0 : ℤ) ?_ ?_ ?_
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
      (Ends.for (T := H * (LightTernaryPairedPotential.time K Λ + 90) + 20) (Q := Inv K base Λ H cols powers cutoff μ H)
        (Inv K base Λ H cols powers cutoff μ) H (LightTernaryPairedPotential.time K Λ + 80) ?_ ?_ ?_ ?_ (hT := by
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
      ?_ (hT := by
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
  · refine ⟨0, μ, ?_, by intro x hx; rfl⟩
    simp [Inv, total, update_frame_setLocal]
    exact (frame_append_zeros ([base, Λ, H, cols, powers, 0, 0] : List ℤ) 1).symm
  · rintro i _ hi _ ⟨ret, ν, rfl, hkeep⟩
    have hiM : i * Λ ^ 4 + Λ ^ 4 ≤ H * Λ ^ 4 := by nlinarith [Nat.mul_le_mul_right (Λ ^ 4) (by omega : i + 1 ≤ H)]
    have hcurrent (q : ℕ) (hq : q < Λ ^ 4) : ν (base + i * Λ ^ 4 + q) = μ (base + i * Λ ^ 4 + q) := hkeep _ (by omega)
    have hp :=
      LightTernaryPairedPotential.meets K (base + i * Λ ^ 4) Λ cols powers ν hPotential hPowers hRow hDigit hDivide
        hPoly hΛ hw (by omega) (by omega) hcols hpowers (Or.inl (by omega)) (Or.inl (by omega)) hApart U hU
        (by intro q hq; rw [hcurrent q hq]; exact hread i hi q hq) hKernelWord hPolyWord
    have hΛ4Nat : Λ ^ 4 ≤ lim.space :=
      by
      have hh : Λ ^ 4 ≤ H * Λ ^ 4 := by simpa only [one_mul] using Nat.mul_le_mul_right (Λ ^ 4) (by omega : 1 ≤ H)
      omega
    have hΛ4Word : (Λ : ℤ) ^ 4 ≤ lim.word := (by exact_mod_cast hΛ4Nat : (Λ : ℤ) ^ 4 ≤ lim.space).trans hw
    have hΛ2Word : (Λ : ℤ) ^ 2 ≤ lim.word :=
      (by exact_mod_cast Nat.pow_le_pow_right hΛ (by decide : 2 ≤ 4) : (Λ : ℤ) ^ 2 ≤ (Λ : ℤ) ^ 4).trans hΛ4Word
    have hΛ3Word : (Λ : ℤ) ^ 3 ≤ lim.word :=
      (by exact_mod_cast Nat.pow_le_pow_right hΛ (by decide : 3 ≤ 4) : (Λ : ℤ) ^ 3 ≤ (Λ : ℤ) ^ 4).trans hΛ4Word
    have hΛ2Pos : 0 ≤ (Λ : ℤ) ^ 2 := by positivity
    have hΛ3Pos : 0 ≤ (Λ : ℤ) ^ 3 := by positivity
    have hΛ4Pos : 0 ≤ (Λ : ℤ) ^ 4 := by positivity
    have hΛ2mul : (Λ : ℤ) * Λ ≤ lim.word := by simpa only [pow_two] using hΛ2Word
    have hΛ3mul : (Λ : ℤ) * Λ * Λ ≤ lim.word := by simpa only [pow_succ, pow_zero, one_mul] using hΛ3Word
    have hΛ4mul : (Λ : ℤ) * Λ * Λ * Λ ≤ lim.word := by simpa only [pow_succ, pow_zero, one_mul] using hΛ4Word
    have hΛ2mulPos : 0 ≤ (Λ : ℤ) * Λ := by positivity
    have hΛ3mulPos : 0 ≤ (Λ : ℤ) * Λ * Λ := by positivity
    have hΛ4mulPos : 0 ≤ (Λ : ℤ) * Λ * Λ * Λ := by positivity
    have hProdEq : (Λ : ℤ) * Λ * Λ * Λ = (Λ : ℤ) ^ 4 := by ring
    have hiProdPos : 0 ≤ (i : ℤ) * ((Λ : ℤ) * Λ * Λ * Λ) := by positivity
    have hiProdWord : (i : ℤ) * ((Λ : ℤ) * Λ * Λ * Λ) ≤ lim.word :=
      by
      rw [hProdEq]
      have hh : i * Λ ^ 4 ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (i : ℤ) * (Λ : ℤ) ^ 4 ≤ lim.space).trans hw
    have haddrWord : (base : ℤ) + (i : ℤ) * ((Λ : ℤ) * Λ * Λ * Λ) ≤ lim.word :=
      by
      rw [hProdEq]
      have hh : base + i * Λ ^ 4 ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (base : ℤ) + (i : ℤ) * (Λ : ℤ) ^ 4 ≤ lim.space).trans hw
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
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, pow_succ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [pow_succ] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, pow_succ] <;> omega)
      on_goal -1 =>
        (rintro result ξ ⟨hresult, hTkeep, hprefix⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hkeep' : Kept μ ξ cutoff := by
      intro x hx
      exact (hprefix x (by omega)).trans (hkeep x hx)
    have he : result = term K base Λ μ i := by
      rw [hresult]
      unfold term LightTernaryPairedPotential.prefixSum
      apply Finset.sum_congr rfl
      intro j hj
      unfold LightTernaryPairedPotential.term
      congr 1
      funext q
      exact
        hcurrent _
          (LightTernaryPairedPolynomial.tensorIndex_lt (WeightEnumeration.digit_lt (by omega))
            (WeightEnumeration.digit_lt (by omega)) (WeightEnumeration.digit_lt (by omega))
            (WeightEnumeration.digit_lt (by omega)))
    have ha := htotal i (by omega)
    have hb := hterm i hi
    have hbWord : |term K base Λ μ i| ≤ lim.word :=
      by
      have hpE : E ≤ (H : ℤ) * E := by nlinarith
      exact hb.trans (hpE.trans (by simpa [E, mul_assoc] using hSumWord))
    have hn := htotal (i + 1) (by omega)
    have ⟨haLo, haHi⟩ := abs_le.mp ha
    have ⟨hbLo, hbHi⟩ := abs_le.mp hbWord
    have ⟨hnLo, hnHi⟩ := abs_le.mp hn
    have hsucc : total K base Λ μ (i + 1) = total K base Λ μ i + term K base Λ μ i := Finset.sum_range_succ _ _
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (total K base Λ μ (i + 1)) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, he, hsucc]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [he, hsucc] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, he, hsucc] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp, result, ξ, ?_, hkeep'⟩
    simp [update_frame_setLocal]
  · intro σ hcounter hinv
    exact hinv
  · rintro i _ hi _ ⟨ret, ν, rfl, hkeep⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  · rintro σ ⟨ret, ν, rfl, hkeep⟩
    have ha := htotal H le_rfl
    have ⟨haLo, haHi⟩ := abs_le.mp ha
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (total K base Λ μ H) ?_ ?_ ?_
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
    exact ⟨rfl, hkeep⟩
end ThreeSum.LightTernaryPairedPotentialBatch
