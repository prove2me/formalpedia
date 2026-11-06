-- Prove2me | solution 1 for QEC.Locality.bkRpowCoefficient_le_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:32:32.977706+00:00
-- url     : https://prove2.me/submissions/03a26b7a-cca4-4285-bbd0-42270155ab25

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Theorems.Thm_QEC_Locality_bkRpowGap_pos
import Theorems.Thm_QEC_Locality_bkEntropyGap_pos
import Theorems.Thm_QEC_Locality_bkEntropyGap_mul_one_sub_le_bkRpowGap

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open Set
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {beta c : ℝ} (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    bkRpowCoefficient beta c ≤
      3 * beta / (bkEntropyGap * (1 - c)) := by
  have hOneSubPos : 0 < 1 - c := sub_pos.mpr hc1
  have hEntropyDenomPos : 0 < bkEntropyGap * (1 - c) :=
    mul_pos bkEntropyGap_pos hOneSubPos
  have hthirdPower : (1 / 3 : ℝ) ≤ (1 / 3 : ℝ) ^ (1 - c) :=
    Real.self_le_rpow_of_le_one (by norm_num) (by norm_num) (by linarith)
  have hgapLower := bkEntropyGap_mul_one_sub_le_bkRpowGap c
  have hgapNonneg : 0 ≤ bkRpowGap c := (bkRpowGap_pos hc0 hc1).le
  have hdenomLower :
      bkEntropyGap * (1 - c) / 3 ≤
        bkRpowGap c * (1 / 3 : ℝ) ^ (1 - c) := by
    calc
      bkEntropyGap * (1 - c) / 3 =
          bkEntropyGap * (1 - c) * (1 / 3 : ℝ) := by ring
      _ ≤ bkRpowGap c * (1 / 3 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hgapLower (by norm_num)
      _ ≤ bkRpowGap c * (1 / 3 : ℝ) ^ (1 - c) :=
        mul_le_mul_of_nonneg_left hthirdPower hgapNonneg
  have hsmallPos : 0 < bkEntropyGap * (1 - c) / 3 := div_pos hEntropyDenomPos (by norm_num)
  have hdiv := div_le_div_of_nonneg_left hbeta hsmallPos hdenomLower
  unfold bkRpowCoefficient
  calc
    beta / (bkRpowGap c * (1 / 3 : ℝ) ^ (1 - c)) ≤
        beta / (bkEntropyGap * (1 - c) / 3) := hdiv
    _ = 3 * beta / (bkEntropyGap * (1 - c)) := by
      field_simp [hEntropyDenomPos.ne']
end QEC.Locality
