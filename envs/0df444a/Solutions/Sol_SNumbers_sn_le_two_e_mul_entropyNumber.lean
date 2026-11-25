-- Prove2me | solution 1 for SNumbers.sn_le_two_e_mul_entropyNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:35:08.223278+00:00
-- url     : https://prove2.me/submissions/d22916cc-923b-4c1c-8a24-caf8e18a7e4f

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
public import Theorems.Thm_SNumbers_hilbertNumber_le_two_mul_entropyNumber
public import Theorems.Thm_SNumbers_isSNumberSequence_hilbertNumber
public import Theorems.Thm_SNumbers_sn_le_e_mul_tn


set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : X →L[𝕜] Y) (n : ℕ) :
    s S n ≤ 2 * Real.exp 1 * ((n : ℝ) + 1) * entropyNumber S n := by
  calc s S n
      ≤ Real.exp 1 * ((n : ℝ) + 1) * hilbertNumber S n :=
        sn_le_e_mul_tn hs isSNumberSequence_hilbertNumber S n
    _ ≤ Real.exp 1 * ((n : ℝ) + 1) * (2 * entropyNumber S n) :=
        mul_le_mul_of_nonneg_left (hilbertNumber_le_two_mul_entropyNumber S n)
          (by positivity)
    _ = 2 * Real.exp 1 * ((n : ℝ) + 1) * entropyNumber S n := by ring
end SNumbers
