-- Prove2me | solution 1 for ThreeSum.Parameters.switch_box_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:41.131827+00:00
-- url     : https://prove2.me/submissions/641bdd84-3252-4428-861d-728690f3c9d1

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
import Definitions.Def_WeightedCache3SUM_Alias_c09f9da662088830

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution {a t : ℝ} (ha : a ∈ Icc (0 : ℝ) terminalFraction)
    (ht : t ∈ Icc (0 : ℝ) (1 / 2)) (hswitch : switchThreshold a ≤ phi t) :
    boxSaving ≤ 2 * bandShift - a + (1 - a) * gamma t := by
  have hden : 0 < 1 - a := by dsimp [terminalFraction] at ha; linarith [ha.2]
  have hs := (div_le_iff₀ hden).mp hswitch
  have hg := mul_le_mul_of_nonneg_left (phi_le_gamma ht) hden.le
  linarith
end ThreeSum.Parameters
