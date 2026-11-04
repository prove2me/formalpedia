-- Prove2me | solution 1 for ThreeSum.Parameters.hasDerivAt_gammaNumerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:42.824395+00:00
-- url     : https://prove2.me/submissions/85061e77-313b-4f4b-9a30-f256ae6c3292

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    HasDerivAt gammaNumerator (Real.log (255 + t) - Real.log (1 - t)) t := by
  have h1 : (1 - t : ℝ) ≠ 0 := by linarith [ht.2]
  have h255 : (255 + t : ℝ) ≠ 0 := by linarith [ht.1]
  have hd1 := (hasDerivAt_id t).const_sub 1
  have hd255 := (hasDerivAt_id t).const_add 255
  have hd := ((hd1.mul (hd1.log h1)).add (hd255.mul (hd255.log h255))).sub_const
    (255 * Real.log 255)
  change HasDerivAt gammaNumerator _ t at hd
  apply hd.congr_deriv
  dsimp only [id_eq]
  field_simp [h1, h255]
  <;> ring
end ThreeSum.Parameters
