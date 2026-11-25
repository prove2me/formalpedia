-- Prove2me | solution 1 for Submodule.liftQL_mkQL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:35:17.030212+00:00
-- url     : https://prove2.me/submissions/1c8059b7-ac68-4b2b-9bbd-ecf232eaf25c

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Group.Quotient
public import Definitions.Def_SNumbers_QuotientMapNorms

set_option autoImplicit true
@[expose] public section
public section
open Submodule
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {Y Z : Type*}
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace Submodule
theorem _root_.solution (V : Submodule 𝕜 Y) (f : Y →L[𝕜] Z)
    (h : V ≤ LinearMap.ker (f : Y →ₗ[𝕜] Z)) (y : Y) :
    V.liftQL f h (V.mkQL y) = f y := by
  rw [V.liftQL_apply, V.mkQL_apply]
  exact V.liftQ_apply (f : Y →ₗ[𝕜] Z) y
end Submodule
