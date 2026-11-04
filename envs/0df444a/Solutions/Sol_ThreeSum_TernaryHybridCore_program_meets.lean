-- Prove2me | solution 1 for ThreeSum.TernaryHybridCore.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:05:09.022175+00:00
-- url     : https://prove2.me/submissions/ec3e1bc7-9e3a-4009-ab01-a20e6095e1e3

import Definitions.Def_Submission_ThreeSum_TernaryHybridResources
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_TernaryHybridCore
import Theorems.Thm_ThreeSum_TernaryHybridCore_main_lookup
import Theorems.Thm_ThreeSum_TernaryHybridCore_power_lookup
import Theorems.Thm_ThreeSum_TernaryHybridCore_brute_meets
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_SolvesN_append
import Theorems.Thm_Light_SolvesN_meets
import Theorems.Thm_Light_Solves_append
import Theorems.Thm_Light_Solves_meets
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Theorems.Thm_ThreeSumApsp_Spec_length_affL
import Theorems.Thm_ThreeSumApsp_Spec_length_subMat
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_ColorClassLists_value_fin
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_fe1d986d2522f297
import Definitions.Def_WeightedCache3SUM_Alias_1b87db5b0e9f9b11
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightClassFilter_items_zero
import Definitions.Def_WeightedCache3SUM_Alias_98152438e5b788f3
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Definitions.Def_WeightedCache3SUM_Alias_6cd6f72823a59258
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Definitions.Def_WeightedCache3SUM_Alias_ec604c008ed4b1df
import Definitions.Def_WeightedCache3SUM_Alias_eb09b223848624eb
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_TernaryHybridResources_brute_of_ok
import Theorems.Thm_ThreeSum_TernaryHybridResources_outer_depth_of_ok
import Theorems.Thm_ThreeSum_TernaryHybridResources_power_word_of_ok
import Theorems.Thm_ThreeSum_TernaryHybridResources_scalar_word_of_ok
import Theorems.Thm_ThreeSum_TernaryHybridResources_source_region_of_ok
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.ColorClassLists.value_fin
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightClassFilter.items_zero
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.Switch.mem_candidates
attribute [local simp] ThreeSumApsp.Spec.length_affL
attribute [local simp] ThreeSumApsp.Spec.length_subMat
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryHybridCore
open Light
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
variable (fastNeed : ℕ → ℕ → Need) (fastTime : ℕ → ℕ)
namespace ThreeSum.TernaryHybridCore
theorem _root_.solution {lim : Limits} {fastP : Program} {fastProc κ cutoff src n U free d : ℕ} (x : Fin n → ℤ)
    (μ : ℕ → ℤ) (hn : 0 < n) (hsrc : src + n ≤ free)
    (H : (TernaryHybridResources.need fastNeed κ cutoff n U).Ok lim free d) (hread : ∀ i : Fin n, μ (src + i.val) = x i)
    (hx : ∀ i, |x i| ≤ (U : ℤ))
    (hfast :
      cutoff ≤ n →
        U ≤ n ^ κ →
          Meets lim fastP fastProc (d + 1) [src, n, free] μ (fastTime n)
            (fun r ν => (r = 0 ∨ r = 1) ∧ (r = 1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free)) :
    Meets lim (program fastP fastProc κ cutoff) (fastP.length + 5) d [n, U, src, free] μ (time fastTime κ cutoff n U)
      (fun r ν => (r = 0 ∨ r = 1) ∧ (r = 1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free) :=
  by
  have hw := H.space
  have hword := TernaryHybridResources.scalar_word_of_ok fastNeed H
  have hd := TernaryHybridResources.outer_depth_of_ok fastNeed H
  have hregions := TernaryHybridResources.source_region_of_ok fastNeed H hsrc
  have hspace := hregions.1
  have hfreeWord := hregions.2
  have hκWord : (κ : ℤ) ≤ lim.word := by omega
  have hpowerWord := TernaryHybridResources.power_word_of_ok fastNeed H (i := κ) le_rfl
  have hpowerCast : ((n ^ κ : ℕ) : ℤ) = (n : ℤ) ^ κ := Nat.cast_pow n κ
  have hb :=
    brute_meets (fastP := fastP) (fastProc := fastProc) (κ := κ) (cutoff := cutoff) x μ hn hsrc
      (TernaryHybridResources.brute_of_ok fastNeed H) hread hx
  have hp :=
    LightNatPower.meets (d := d + 1) (b := n) (e := κ) (power_lookup fastP fastProc κ cutoff) μ hκWord
      (fun i hi => TernaryHybridResources.power_word_of_ok fastNeed H hi)
  by_cases hsmall : n < cutoff
  · rw [time, if_pos (Or.inl hsmall)]
    apply Meets.of_body (main_lookup fastP fastProc κ cutoff)
    unfold body
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.iteIffThen (n < cutoff) (fun hyes => ?_) (fun hno => ?_) ?_ ?_
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
      all_goals
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
    · focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        first
        | refine _root_.Light.Ends.callToThen (hb _ (by omega)) ?_ ?_ ?_ ?_
        | refine _root_.Light.Ends.callToThen hb ?_ ?_ ?_ ?_
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
        on_goal -1 => (rintro r ν ⟨hbool, hcorrect, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      subst ν
      exact ⟨hbool, hcorrect, SameOn.refl⟩
    · omega
  · by_cases hlarge : n ^ κ < U
    · rw [time, if_pos (Or.inr hlarge)]
      apply Meets.of_body (main_lookup fastP fastProc κ cutoff)
      unfold body
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        refine _root_.Light.Ends.iteIffThen (n < cutoff) (fun hyes => ?_) (fun hno => ?_) ?_ ?_
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
        all_goals
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
      · omega
      · focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            (repeat
                with_unfolding_none
                  first
                  | refine _root_.Light.Ends.seqAssoc ?_
                  | refine _root_.Light.Ends.skipThen ?_))
          first
          | refine _root_.Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
          | refine _root_.Light.Ends.callToThen hp ?_ ?_ ?_ ?_
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
          on_goal -1 => (rintro power ν ⟨hpower, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
        subst ν
        subst power
        focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            (repeat
                with_unfolding_none
                  first
                  | refine _root_.Light.Ends.seqAssoc ?_
                  | refine _root_.Light.Ends.skipThen ?_))
          refine _root_.Light.Ends.iteIffThen (n ^ κ < U) (fun hyesU => ?_) (fun hnoU => ?_) ?_ ?_
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
          all_goals
            (repeat
                with_unfolding_none
                  first
                  | refine _root_.Light.Ends.seqAssoc ?_
                  | refine _root_.Light.Ends.skipThen ?_)
        · focus
            ((first
                | refine _root_.Light.Ends.seqSelf ?_
                | refine _root_.Light.Ends.skipLast ?_);
              (repeat
                  with_unfolding_none
                    first
                    | refine _root_.Light.Ends.seqAssoc ?_
                    | refine _root_.Light.Ends.skipThen ?_))
            first
            | refine _root_.Light.Ends.callToThen (hb _ (by omega)) ?_ ?_ ?_ ?_
            | refine _root_.Light.Ends.callToThen hb ?_ ?_ ?_ ?_
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
            on_goal -1 => (rintro r ξ ⟨hbool, hcorrect, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
          subst ξ
          exact ⟨hbool, hcorrect, SameOn.refl⟩
        · omega
    · rw [time, if_neg (not_or_intro hsmall hlarge)]
      have hf :=
        (hfast (by omega) (by omega)).append
          (LightBruteThreeSum.program.map (ReportingHostRelocation.relocate fastP.length) ++
            [LightNatPower.body, body fastP.length fastProc κ cutoff])
      have hf' :
        Meets lim (program fastP fastProc κ cutoff) fastProc (d + 1) [src, n, free] μ (fastTime n)
          (fun r ν => (r = 0 ∨ r = 1) ∧ (r = 1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free) :=
        by simpa only [program, libraries, ReportingHostRelocation.program, List.append_assoc] using hf
      apply Meets.of_body (main_lookup fastP fastProc κ cutoff)
      unfold body
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        refine _root_.Light.Ends.iteIffThen (n < cutoff) (fun hyes => ?_) (fun hno => ?_) ?_ ?_
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
        all_goals
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
      · omega
      · focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            (repeat
                with_unfolding_none
                  first
                  | refine _root_.Light.Ends.seqAssoc ?_
                  | refine _root_.Light.Ends.skipThen ?_))
          first
          | refine _root_.Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
          | refine _root_.Light.Ends.callToThen hp ?_ ?_ ?_ ?_
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
          on_goal -1 => (rintro power ν ⟨hpower, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
        subst ν
        subst power
        focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            (repeat
                with_unfolding_none
                  first
                  | refine _root_.Light.Ends.seqAssoc ?_
                  | refine _root_.Light.Ends.skipThen ?_))
          refine _root_.Light.Ends.iteIffThen (n ^ κ < U) (fun hyesU => ?_) (fun hnoU => ?_) ?_ ?_
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
          all_goals
            (repeat
                with_unfolding_none
                  first
                  | refine _root_.Light.Ends.seqAssoc ?_
                  | refine _root_.Light.Ends.skipThen ?_)
        · omega
        · focus
            ((first
                | refine _root_.Light.Ends.seqSelf ?_
                | refine _root_.Light.Ends.skipLast ?_);
              (repeat
                  with_unfolding_none
                    first
                    | refine _root_.Light.Ends.seqAssoc ?_
                    | refine _root_.Light.Ends.skipThen ?_))
            first
            | refine _root_.Light.Ends.callToThen (hf' _ (by omega)) ?_ ?_ ?_ ?_
            | refine _root_.Light.Ends.callToThen hf' ?_ ?_ ?_ ?_
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
            on_goal -1 => (rintro r ξ hh; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
          exact hh
end ThreeSum.TernaryHybridCore
