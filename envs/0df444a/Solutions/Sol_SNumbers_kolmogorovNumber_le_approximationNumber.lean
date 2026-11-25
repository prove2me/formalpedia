-- Prove2me | solution 1 for SNumbers.kolmogorovNumber_le_approximationNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:19:45.370988+00:00
-- url     : https://prove2.me/submissions/e598a0e7-eda2-40c5-8240-c67e355b7433

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
public import Theorems.Thm_SNumbers_isSNumberSequence_kolmogorovNumber
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
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S n ≤ approximationNumber S n :=
  sn_le_approximationNumber isSNumberSequence_kolmogorovNumber S n
end SNumbers
