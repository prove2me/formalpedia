-- Prove2me | solution 1 for SNumbers.norm_comp_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:35:30.980825+00:00
-- url     : https://prove2.me/submissions/781b53cd-520c-472e-88e8-de7e6a2e6d49

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_Hilbert

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y W Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution {W' X' Y' Z' : Type*}
    [NormedAddCommGroup W'] [NormedSpace 𝕜 W'] [NormedAddCommGroup X'] [NormedSpace 𝕜 X']
    [NormedAddCommGroup Y'] [NormedSpace 𝕜 Y'] [NormedAddCommGroup Z'] [NormedSpace 𝕜 Z']
    (A : W' →L[𝕜] X') (S : X' →L[𝕜] Y') (B : Y' →L[𝕜] Z') :
    ‖B.comp (S.comp A)‖ ≤ ‖B‖ * ‖S‖ * ‖A‖ := by
  calc ‖B.comp (S.comp A)‖
      ≤ ‖B‖ * ‖S.comp A‖ := opNorm_comp_le _ _
    _ ≤ ‖B‖ * (‖S‖ * ‖A‖) := by gcongr; exact opNorm_comp_le _ _
    _ = ‖B‖ * ‖S‖ * ‖A‖ := by ring
end SNumbers
