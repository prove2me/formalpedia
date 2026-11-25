-- Prove2me | solution 1 for SNumbers.entropyNumber_zero_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:22:43.191848+00:00
-- url     : https://prove2.me/submissions/53137ba9-cdc8-4760-b67a-c251cca20268

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
public import Theorems.Thm_SNumbers_norm_le_of_mem_entropySet_zero
public import Theorems.Thm_SNumbers_entropyNumber_def
public import Theorems.Thm_SNumbers_entropyNumber_le_norm
public import Theorems.Thm_SNumbers_entropySet_nonempty


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
theorem _root_.solution (S : X →L[𝕜] Y) : entropyNumber S 0 = ‖S‖ :=
  le_antisymm (entropyNumber_le_norm S 0)
    (by rw [entropyNumber_def]
        exact le_csInf (entropySet_nonempty S 0) fun ε hε => norm_le_of_mem_entropySet_zero hε)
end SNumbers
