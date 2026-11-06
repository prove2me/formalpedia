-- Prove2me | solution 1 for QEC.Locality.bkRpowPotential_eq_source_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:37:01.236212+00:00
-- url     : https://prove2.me/submissions/5261bfde-4540-4f38-8391-6c75b17d8aed

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open Set
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {beta c : ℝ} {d parent : Nat} (hd : 0 < d) :
    bkRpowPotential beta c d parent =
      bkRpowCoefficient beta c * parent / (d : ℝ) ^ (1 - c) -
        (beta / bkRpowGap c) * (parent : ℝ) ^ c := by
  have hdReal : (0 : ℝ) < d := by exact_mod_cast hd
  have hdPowC : 0 < (d : ℝ) ^ c := Real.rpow_pos_of_pos hdReal _
  have hdPowOneSub : 0 < (d : ℝ) ^ (1 - c) := Real.rpow_pos_of_pos hdReal _
  have hdFactor : (d : ℝ) ^ c * (d : ℝ) ^ (1 - c) = d := by
    rw [← Real.rpow_add hdReal]
    ring_nf
    exact Real.rpow_one d
  have hparentRpow : (d : ℝ) ^ c * ((parent : ℝ) / d) ^ c =
      (parent : ℝ) ^ c := by
    rw [Real.div_rpow (Nat.cast_nonneg parent) hdReal.le]
    field_simp
  have hparentLinear : (d : ℝ) ^ c * ((parent : ℝ) / d) =
      (parent : ℝ) / (d : ℝ) ^ (1 - c) := by
    apply (eq_div_iff hdPowOneSub.ne').2
    calc
      ((d : ℝ) ^ c * ((parent : ℝ) / d)) * (d : ℝ) ^ (1 - c) =
          (parent : ℝ) / d * ((d : ℝ) ^ c * (d : ℝ) ^ (1 - c)) := by ring
      _ = (parent : ℝ) := by rw [hdFactor]; field_simp
  unfold bkRpowPotential bkRpowCoefficient
  rw [mul_sub]
  rw [mul_assoc (beta / bkRpowGap c) ((d : ℝ) ^ c)
    (((parent : ℝ) / d) ^ c), hparentRpow]
  rw [show (beta / bkRpowGap c) * (d : ℝ) ^ c *
      ((parent : ℝ) / d / (1 / 3 : ℝ) ^ (1 - c)) =
      (beta / bkRpowGap c) *
        ((d : ℝ) ^ c * ((parent : ℝ) / d)) /
          (1 / 3 : ℝ) ^ (1 - c) by ring]
  rw [hparentLinear]
  have haPow : (1 / 3 : ℝ) ^ (1 - c) ≠ 0 :=
    (Real.rpow_pos_of_pos (by norm_num) _).ne'
  field_simp [haPow]
end QEC.Locality
