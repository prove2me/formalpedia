-- Prove2me | solution 1 for SNumbers.max_gelfandNumber_kolmogorovNumber_le_e_mul_hilbertNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:32:47.851944+00:00
-- url     : https://prove2.me/submissions/da901c40-9242-4f19-a674-800ffa809c0c

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
public import Theorems.Thm_SNumbers_max_gelfandNumber_kolmogorovNumber_le_e_mul_sn
public import Theorems.Thm_SNumbers_isSNumberSequence_hilbertNumber


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
theorem _root_.solution
    (S : X →L[𝕜] Y) (n : ℕ) :
    max (gelfandNumber S n) (kolmogorovNumber S n)
      ≤ Real.exp 1 * ((n : ℝ) + 1) * hilbertNumber S n :=
  max_gelfandNumber_kolmogorovNumber_le_e_mul_sn
    isSNumberSequence_hilbertNumber S n
end SNumbers
