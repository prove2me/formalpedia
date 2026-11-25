-- Prove2me | solution 1 for SNumbers.approximationNumber_le_e_mul_sn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:26:58.415096+00:00
-- url     : https://prove2.me/submissions/c771c444-2a8c-40f5-a6b9-4794d88380a7

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
public import Theorems.Thm_SNumbers_approximationNumber_le_e_mul_hilbertNumber
public import Theorems.Thm_SNumbers_hilbertNumber_le_sn


set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open scoped Pointwise
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤ Real.exp 1 * ((n : ℝ) + 1) * s S n :=
  (approximationNumber_le_e_mul_hilbertNumber S n).trans
    (mul_le_mul_of_nonneg_left (hilbertNumber_le_sn hs S n) (by positivity))
end SNumbers
