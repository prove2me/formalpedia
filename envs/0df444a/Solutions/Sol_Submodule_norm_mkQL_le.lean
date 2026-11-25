-- Prove2me | solution 1 for Submodule.norm_mkQL_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:12:46.858802+00:00
-- url     : https://prove2.me/submissions/b7b51278-a30f-43a3-97f9-224dd776a3a9

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
theorem _root_.solution (V : Submodule 𝕜 Y) : ‖V.mkQL‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul, V.mkQL_apply, mkQ_apply]
    exact _root_.Submodule.Quotient.norm_mk_le (S := V) x
end Submodule
