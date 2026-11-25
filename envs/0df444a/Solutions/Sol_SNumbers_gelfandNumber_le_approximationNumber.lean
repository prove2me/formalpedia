-- Prove2me | solution 1 for SNumbers.gelfandNumber_le_approximationNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:19:43.881417+00:00
-- url     : https://prove2.me/submissions/ee50f736-b9b2-4e97-b278-6f9961f047fe

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
public import Theorems.Thm_SNumbers_isSNumberSequence_gelfandNumber
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
    gelfandNumber S n ≤ approximationNumber S n :=
  sn_le_approximationNumber isSNumberSequence_gelfandNumber S n
end SNumbers
