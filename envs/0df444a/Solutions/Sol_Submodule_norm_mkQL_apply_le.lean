-- Prove2me | solution 1 for Submodule.norm_mkQL_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:23:03.366075+00:00
-- url     : https://prove2.me/submissions/f16dac88-2370-4a23-80da-e40d39a03931

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
theorem _root_.solution (V : Submodule 𝕜 Y) (y : Y) : ‖V.mkQL y‖ ≤ ‖y‖ := by
  rw [V.mkQL_apply, mkQ_apply]
  exact _root_.Submodule.Quotient.norm_mk_le (S := V) y
end Submodule
