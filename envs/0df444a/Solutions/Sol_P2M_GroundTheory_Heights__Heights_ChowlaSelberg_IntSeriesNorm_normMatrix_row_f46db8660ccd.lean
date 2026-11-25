-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_normMatrix_row_f46db8660ccd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:38.296606+00:00
-- url     : https://prove2.me/submissions/4e199bca-984f-4042-9dd4-54b81cf6e265

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PIntSeriesNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_intSeriesEval_X_5d0b12571f15
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_intSeriesConv_X_3201b112e74d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_residuePart_conv_7c24ca73e8b7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_intSeriesEval_split_252472cd49a8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ChowlaSelberg
open PowerSeries
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesNorm
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesNorm
theorem _root_.solution (hR : IntSeriesRing.Statement) {F : PowerSeries ℤ} {r : ℝ} (hr : 0 < r)
    (hF : IntSeriesConv F r) {p : ℕ} [NeZero p] (s : ℂ) (hs : ‖s‖ ≤ r) (i : Fin p) :
    ∑ k : Fin p, intSeriesEval (normMatrix F p i k) (s ^ p) * s ^ (k : ℕ) =
      s ^ (i : ℕ) * intSeriesEval F s := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  obtain ⟨-, hmul, -, -, -⟩ := hR (r ^ p) (pow_nonneg hr.le p)
  have hq : ‖s ^ p‖ ≤ r ^ p := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hs p
  have hentry : ∀ k : Fin p, intSeriesEval (normMatrix F p i k) (s ^ p) =
      (if i ≤ k then 1 else s ^ p) * intSeriesEval (residuePart F p ((k - i : Fin p) : ℕ)) (s ^ p) := by
    intro k
    simp only [normMatrix, Matrix.of_apply]
    split_ifs
    · rw [one_mul, one_mul]
    · rw [hmul _ _ (intSeriesConv_X _) (residuePart_conv hr hF hp _) _ hq, intSeriesEval_X]
  rw [intSeriesEval_split hR hr hF hp s hs, Finset.mul_sum]
  symm
  apply Fintype.sum_equiv (Equiv.addLeft i)
  intro k
  simp only [Equiv.coe_addLeft]
  rw [hentry, add_sub_cancel_left]
  have hi := i.is_lt
  have hk := k.is_lt
  by_cases h : (i : ℕ) + k < p
  · have hv : ((i + k : Fin p) : ℕ) = i + k := by rw [Fin.val_add, Nat.mod_eq_of_lt h]
    have hle : i ≤ i + k := by rw [Fin.le_iff_val_le_val, hv]; omega
    rw [if_pos hle, hv, pow_add]
    ring
  · have hv : ((i + k : Fin p) : ℕ) = i + k - p := by
      rw [Fin.val_add, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hnle : ¬ i ≤ i + k := by rw [Fin.le_iff_val_le_val, hv]; omega
    rw [if_neg hnle, hv]
    have hpow : s ^ ((i : ℕ) + k) = s ^ p * s ^ ((i : ℕ) + k - p) := by
      rw [← pow_add]; congr 1; omega
    generalize intSeriesEval (residuePart F p k) (s ^ p) = G
    calc s ^ (i : ℕ) * (s ^ (k : ℕ) * G) = s ^ ((i : ℕ) + k) * G := by rw [pow_add]; ring
      _ = _ := by rw [hpow]; ring
end GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesNorm
