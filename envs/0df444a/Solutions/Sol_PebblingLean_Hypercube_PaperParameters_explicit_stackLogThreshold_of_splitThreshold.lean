-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.explicit_stackLogThreshold_of_splitThreshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:13:03.191907+00:00
-- url     : https://prove2.me/submissions/ad60b576-6e8b-41d5-9a25-9b3261b67ee1

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stackMargin_pos
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_one_twentieth_le_stackMargin

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {n0 : ℕ}
    (hsplitThreshold : (128 * (217 : ℝ) ^ 2) ^ 2 ≤ (n0 : ℝ)) :
    (32 / stackMargin ^ 2) ^ 2 ≤ (n0 : ℝ) := by
  have hc_pos : 0 < stackMargin := stackMargin_pos
  have hcLower : (1 : ℝ) / 20 ≤ stackMargin := one_twentieth_le_stackMargin
  have hcSqLower : ((1 : ℝ) / 20) ^ 2 ≤ stackMargin ^ 2 :=
    (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 20) hc_pos.le).mpr
      hcLower
  have hcoefLe : 32 / stackMargin ^ 2 ≤ (12800 : ℝ) := by
    rw [div_le_iff₀ (sq_pos_of_pos hc_pos)]
    nlinarith
  have hcoef_nonneg : 0 ≤ 32 / stackMargin ^ 2 := by positivity
  have hsqLe :
      (32 / stackMargin ^ 2) ^ 2 ≤ (12800 : ℝ) ^ 2 :=
    (sq_le_sq₀ hcoef_nonneg (by norm_num : (0 : ℝ) ≤ 12800)).mpr hcoefLe
  have hbig :
      (12800 : ℝ) ^ 2 ≤ (128 * (217 : ℝ) ^ 2) ^ 2 := by
    norm_num
  exact hsqLe.trans (hbig.trans hsplitThreshold)
end PebblingLean.Hypercube.PaperParameters
