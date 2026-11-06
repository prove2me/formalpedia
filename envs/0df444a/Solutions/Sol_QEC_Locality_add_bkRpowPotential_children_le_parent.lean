-- Prove2me | solution 1 for QEC.Locality.add_bkRpowPotential_children_le_parent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:32:15.306442+00:00
-- url     : https://prove2.me/submissions/d8f58f51-9c89-4e5c-8175-46fb208a4c93

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Theorems.Thm_QEC_Locality_bkRpowGap_pos
import Theorems.Thm_QEC_Locality_bkRpowGap_mul_parent_le_children_gap
import Theorems.Thm_QEC_Locality_beta_div_bkRpowGap_nonneg
import Theorems.Thm_QEC_Locality_bkRpowPotential_eq_source_form

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open Set
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι)
    {beta c : ℝ} {d parent left right : Nat}
    (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1) (hd : 0 < d)
    (hparent : 0 < parent) (hsum : left + right = parent)
    (hleftLower : parent ≤ 3 * left) (hleftUpper : 3 * left ≤ 2 * parent)
    (hcharge : (twoThirdsSeparationProfile G parent : ℝ) ≤
      beta * (parent : ℝ) ^ c) :
    (twoThirdsSeparationProfile G parent : ℝ) +
        bkRpowPotential beta c d left + bkRpowPotential beta c d right ≤
      bkRpowPotential beta c d parent := by
  have hparentReal : (0 : ℝ) < parent := by exact_mod_cast hparent
  have hsumReal : (left : ℝ) + right = parent := by exact_mod_cast hsum
  have hleftLowerReal : (parent : ℝ) / 3 ≤ left := by
    have h : (parent : ℝ) ≤ 3 * left := by exact_mod_cast hleftLower
    linarith
  have hleftUpperReal : (left : ℝ) ≤ 2 * parent / 3 := by
    have h : 3 * (left : ℝ) ≤ 2 * parent := by exact_mod_cast hleftUpper
    linarith
  have hgap := bkRpowGap_mul_parent_le_children_gap hc0 hc1.le
    hparentReal hsumReal hleftLowerReal hleftUpperReal
  have hfactor : 0 ≤ beta / bkRpowGap c :=
    beta_div_bkRpowGap_nonneg hbeta hc0 hc1
  have hscaled := mul_le_mul_of_nonneg_left hgap hfactor
  have hgapNe : bkRpowGap c ≠ 0 := (bkRpowGap_pos hc0 hc1).ne'
  have hchargeScaled :
      beta * (parent : ℝ) ^ c ≤
        (beta / bkRpowGap c) *
          ((left : ℝ) ^ c + (right : ℝ) ^ c - (parent : ℝ) ^ c) := by
    calc
      beta * (parent : ℝ) ^ c =
          (beta / bkRpowGap c) *
            (bkRpowGap c * (parent : ℝ) ^ c) := by
        field_simp [hgapNe]
      _ ≤ (beta / bkRpowGap c) *
          ((left : ℝ) ^ c + (right : ℝ) ^ c - (parent : ℝ) ^ c) := hscaled
  rw [bkRpowPotential_eq_source_form hd,
    bkRpowPotential_eq_source_form hd,
    bkRpowPotential_eq_source_form hd]
  have hdPowNe : (d : ℝ) ^ (1 - c) ≠ 0 :=
    (Real.rpow_pos_of_pos (by exact_mod_cast hd) _).ne'
  have hlinear :
      bkRpowCoefficient beta c * (left : ℝ) / (d : ℝ) ^ (1 - c) +
          bkRpowCoefficient beta c * (right : ℝ) / (d : ℝ) ^ (1 - c) =
        bkRpowCoefficient beta c * (parent : ℝ) / (d : ℝ) ^ (1 - c) := by
    rw [← add_div, ← mul_add, hsumReal]
  linarith [hchargeScaled]
end QEC.Locality
