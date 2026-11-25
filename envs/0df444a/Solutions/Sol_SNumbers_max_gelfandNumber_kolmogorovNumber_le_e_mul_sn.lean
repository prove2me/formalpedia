-- Prove2me | solution 1 for SNumbers.max_gelfandNumber_kolmogorovNumber_le_e_mul_sn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:29:11.222081+00:00
-- url     : https://prove2.me/submissions/c67b4495-a063-4430-b8b7-87de8954bb65

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
public import Theorems.Thm_SNumbers_approximationNumber_le_e_mul_sn
public import Theorems.Thm_SNumbers_gelfandNumber_le_approximationNumber
public import Theorems.Thm_SNumbers_kolmogorovNumber_le_approximationNumber

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
theorem _root_.solution {s : Family 𝕜}
    (hs : IsSNumberSequence s) (S : X →L[𝕜] Y) (n : ℕ) :
    max (gelfandNumber S n) (kolmogorovNumber S n)
      ≤ Real.exp 1 * ((n : ℝ) + 1) * s S n :=
  max_le
    ((gelfandNumber_le_approximationNumber S n).trans
      (approximationNumber_le_e_mul_sn hs S n))
    ((kolmogorovNumber_le_approximationNumber S n).trans
      (approximationNumber_le_e_mul_sn hs S n))
end SNumbers
