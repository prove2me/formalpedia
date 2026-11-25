-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_RestTerms_IntegerTail_intersectionNumber_baseChange_3ef0d4b49ae9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:57:23.864295+00:00
-- url     : https://prove2.me/submissions/5ceaccb9-1be6-4d32-986b-640253356d53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PrimeWeightEqZeroOfLt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_TenNinthsLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_intWeight_nonneg_546dc8b33f2f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_log_div_sq_le_phiT_sub_469330899d5f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_phiT_nonneg_7a19d717162f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.RestTerms
open Finset GroundTheory.Heights₂.Heights.RestTerms.Elem
noncomputable section
namespace IntegerTail
private theorem w_nonneg (m : ℕ) : 0 ≤ w m :=
  div_nonneg (Real.log_natCast_nonneg m) (by positivity)
private theorem sum_Ioc_le (c : ℕ) (hc : 3 ≤ c) (j : ℕ) :
    ∑ m ∈ Ioc c (c + j), w m ≤ phiT (c : ℝ) - phiT ((c + j : ℕ) : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show c + (j + 1) = (c + j) + 1 by omega, Finset.sum_Ioc_succ_top (by omega)]
    have hk := log_div_sq_le_phiT_sub ((c + j : ℕ) : ℝ)
      (by exact_mod_cast (show 3 ≤ c + j by omega))
    have e : ((c + j + 1 : ℕ) : ℝ) = ((c + j : ℕ) : ℝ) + 1 := by push_cast; ring
    unfold w
    rw [e]
    unfold w at ih
    linarith
private theorem sum_Ioc_le' (a c : ℕ) (hac : a ≤ c) (hc : 3 ≤ c) (K : ℕ) :
    ∑ m ∈ Ioc a (c + K), w m ≤ ∑ m ∈ Ioc a c, w m + phiT (c : ℝ) := by
  rw [← Finset.sum_Ioc_consecutive _ hac (Nat.le_add_right c K)]
  have h1 := sum_Ioc_le c hc K
  have h2 := phiT_nonneg (t := ((c + K : ℕ) : ℝ)) (by exact_mod_cast (show 1 ≤ c + K by omega))
  linarith
private theorem ten_ninths_le (B : ℝ) (h1 : 1 ≤ B) (h3 : B ≤ 3) :
    10 / 9 ≤ 2 * (1 + Real.log B) / B := by
  have hB : 0 < B := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hB
  have hBl : B - 1 ≤ B * Real.log B := by
    have : B * (1 - B⁻¹) = B - 1 := by field_simp
    nlinarith
  rw [le_div_iff₀ hB]
  nlinarith [mul_nonneg (show 0 ≤ 3 - B by linarith) (show 0 ≤ 10 * B - 6 by linarith)]
private theorem head_le : w 2 + w 3 + phiT (3 : ℝ) ≤ 10 / 9 := by
  have h2 := Real.log_two_lt_d9
  have h34 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 4 by norm_num)
  have h3 : Real.log 3 ≤ 2 * Real.log 2 - 1 / 4 := by
    have : Real.log (3 / 4) = Real.log 3 - 2 * Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    linarith
  unfold w phiT
  push_cast
  norm_num
  linarith
private theorem partial_le (B : ℝ) (hB : 1 ≤ B) (K : ℕ) :
    ∑ m ∈ range K, intWeight B m ≤ 2 * (1 + Real.log B) / B := by
  set n := ⌊B⌋₊ with hn
  have hB0 : 0 < B := by linarith
  have hnle : (n : ℝ) ≤ B := Nat.floor_le hB0.le
  have hnlt : B < (n : ℝ) + 1 := Nat.lt_floor_add_one B
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hB)

  have hsub : ∀ c, n ≤ c → ∑ m ∈ range K, intWeight B m ≤ ∑ m ∈ Ioc n (c + K), w m := by
    intro c hc
    have : ∑ m ∈ range K, intWeight B m = ∑ m ∈ (range K).filter (fun m : ℕ => B < m), w m := by
      rw [Finset.sum_filter]; rfl
    rw [this]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      rw [Finset.mem_filter, Finset.mem_range] at hm
      rw [Finset.mem_Ioc]
      have : (n : ℝ) < m := lt_of_le_of_lt hnle hm.2
      constructor
      · exact_mod_cast this
      · omega
    · intro m _ _
      exact w_nonneg m
  rcases le_or_gt 3 n with h3 | h3
  · refine (hsub n le_rfl).trans ?_
    refine (sum_Ioc_le' n n le_rfl h3 K).trans ?_
    simp only [Finset.Ioc_self, Finset.sum_empty, zero_add]
    unfold phiT
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hlog : Real.log n ≤ Real.log B := Real.log_le_log (by linarith) hnle
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1'
    rw [div_le_div_iff₀ (by linarith) hB0]
    nlinarith
  · refine (hsub 3 h3.le).trans ?_
    have hIoc : ∑ m ∈ Ioc n (3 + K), w m ≤ ∑ m ∈ Ioc 1 (3 + K), w m :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_left hn1)
        (fun m _ _ => w_nonneg m)
    refine hIoc.trans ((sum_Ioc_le' 1 3 (by norm_num) le_rfl K).trans ?_)
    have hpair : ∑ m ∈ Ioc 1 3, w m = w 2 + w 3 := by
      rw [show Ioc 1 3 = {2, 3} by decide, Finset.sum_pair (by norm_num)]
    rw [hpair]
    have hB3 : B ≤ 3 := by
      have : (n : ℝ) ≤ 2 := by exact_mod_cast (show n ≤ 2 by omega)
      linarith
    exact head_le.trans (ten_ninths_le B hB hB3)
end IntegerTail
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.RestTerms
end

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.RestTerms
open Finset GroundTheory.Heights₂.Heights.RestTerms.Elem
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.RestTerms
namespace IntegerTail
theorem _root_.solution : IntegerTail.Statement := by
  intro B hB
  set s : Set ℕ := {m | B < m}
  have hind : s.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ 2) = intWeight B := by
    funext m
    by_cases h : B < m
    · simp [s, Set.indicator_of_mem, h, intWeight]
    · simp [s, Set.indicator_of_notMem, h, intWeight]
  have hsum : Summable (intWeight B) :=
    summable_of_sum_range_le (intWeight_nonneg B) (IntegerTail.partial_le B hB)
  have hsub : Summable (fun m : s => Real.log m / (m : ℝ) ^ 2) :=
    (summable_subtype_iff_indicator (f := fun m : ℕ => Real.log m / (m : ℝ) ^ 2)
      (s := s)).mpr (by rw [hind]; exact hsum)
  refine ⟨hsub, ?_⟩
  have : ∑' m : s, Real.log m / (m : ℝ) ^ 2 ≤ 2 * (1 + Real.log B) / B := by
    rw [tsum_subtype s (fun m : ℕ => Real.log m / (m : ℝ) ^ 2), hind]
    exact Real.tsum_le_of_sum_range_le (intWeight_nonneg B) (IntegerTail.partial_le B hB)
  exact this
end IntegerTail
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.RestTerms
