-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.loss_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:56:20.830726+00:00
-- url     : https://prove2.me/submissions/9d4b5f0d-8467-48ea-849e-c51f5bb441a6

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    loss n ≤ loss m := by
  unfold loss
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hn_pos_nat : 0 < n := lt_of_lt_of_le hm hmn
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hmn_real : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hsq : (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith [hmn_real, sq_nonneg ((n : ℝ) - m)]
  exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hsq
end PebblingLean.Hypercube.PaperParameters
