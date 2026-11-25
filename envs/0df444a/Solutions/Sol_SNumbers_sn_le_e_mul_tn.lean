-- Prove2me | solution 1 for SNumbers.sn_le_e_mul_tn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:29:15.168602+00:00
-- url     : https://prove2.me/submissions/4e07b586-1d45-4aea-bc96-a3faacbd9247

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
public import Theorems.Thm_SNumbers_approximationNumber_le_e_mul_sn
public import Theorems.Thm_SNumbers_sn_le_approximationNumber


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
theorem _root_.solution {s t : Family 𝕜} (hs : IsSNumberSequence s)
    (ht : IsSNumberSequence t) (S : X →L[𝕜] Y) (n : ℕ) :
    s S n ≤ Real.exp 1 * ((n : ℝ) + 1) * t S n :=
  (sn_le_approximationNumber hs S n).trans
    (approximationNumber_le_e_mul_sn ht S n)
end SNumbers
