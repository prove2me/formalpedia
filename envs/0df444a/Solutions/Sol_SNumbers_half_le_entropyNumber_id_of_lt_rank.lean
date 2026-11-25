-- Prove2me | solution 1 for SNumbers.half_le_entropyNumber_id_of_lt_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:56:28.936987+00:00
-- url     : https://prove2.me/submissions/4aaf1af8-9a85-4ac4-ac9a-dee8eb88b9d8

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
public import Theorems.Thm_SNumbers_half_le_entropyNumber_id
public import Theorems.Thm_SNumbers_half_le_entropyNumber_id_of_not_finiteDimensional

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
open MeasureTheory
namespace SNumbers
theorem _root_.solution (X : Type u) [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] {n : ℕ} (hn : (n : Cardinal) < Module.rank 𝕜 X) :
    1 / 2 ≤ entropyNumber (ContinuousLinearMap.id 𝕜 X) n := by
  by_cases hX : FiniteDimensional 𝕜 X
  · rw [← Module.finrank_eq_rank, Nat.cast_lt] at hn
    exact half_le_entropyNumber_id X hn
  · exact half_le_entropyNumber_id_of_not_finiteDimensional X hX n
end SNumbers
