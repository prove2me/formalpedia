-- Prove2me | solution 1 for SNumbers.max_gelfandNumber_kolmogorovNumber_le_succ_mul_entropyNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:51:50.788425+00:00
-- url     : https://prove2.me/submissions/a440bd2b-c4fb-424b-8750-dae993c38d58

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
public import Theorems.Thm_SNumbers_kolmogorovNumber_le_succ_mul_entropyNumber
public import Theorems.Thm_SNumbers_gelfandNumber_le_succ_mul_entropyNumber

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
theorem _root_.solution
    (S : X →L[𝕜] Y) (n : ℕ) :
    max (gelfandNumber S n) (kolmogorovNumber S n) ≤
      ((n : ℝ) + 1) * entropyNumber S n :=
  max_le (gelfandNumber_le_succ_mul_entropyNumber S n)
    (kolmogorovNumber_le_succ_mul_entropyNumber S n)
end SNumbers
