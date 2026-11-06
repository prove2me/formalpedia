-- Prove2me | solution 1 for QEC.Locality.bkSumPreservingRecurrence_cast_le_bkRpowCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:38:01.806966+00:00
-- url     : https://prove2.me/submissions/5f9b8f97-c942-4c78-8e60-c4d468f3f9c4

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Theorems.Thm_QEC_Locality_beta_div_bkRpowGap_nonneg
import Theorems.Thm_QEC_Locality_bkRpowPotential_eq_source_form
import Theorems.Thm_QEC_Locality_bkSumPreservingRecurrence_cast_le_bkRpowPotential

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open Set
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (d root parent : Nat) (beta c : ℝ)
    (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1) (hd : 2 ≤ d)
    (hparent : d ≤ parent) (hroot : parent ≤ root)
    (hprofile : ∀ scale : Nat, d ≤ scale → scale ≤ root →
      (twoThirdsSeparationProfile G scale : ℝ) ≤ beta * (scale : ℝ) ^ c) :
    (bkSumPreservingRecurrence G d parent : ℝ) ≤
      bkRpowCoefficient beta c * parent / (d : ℝ) ^ (1 - c) := by
  have hpotential := bkSumPreservingRecurrence_cast_le_bkRpowPotential
    G d root parent beta c hbeta hc0 hc1 hd hparent hroot hprofile
  rw [bkRpowPotential_eq_source_form (by omega)] at hpotential
  have hsubtracted : 0 ≤
      (beta / bkRpowGap c) * (parent : ℝ) ^ c :=
    mul_nonneg (beta_div_bkRpowGap_nonneg hbeta hc0 hc1)
      (Real.rpow_nonneg (Nat.cast_nonneg parent) c)
  linarith
end QEC.Locality
