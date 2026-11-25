-- Prove2me | solution 1 for SNumbers.gainOnSubspace_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:12:57.307798+00:00
-- url     : https://prove2.me/submissions/07118978-1c2c-47c2-9919-6fba93b4fa33

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Definitions.Def_SNumbers_Bernstein

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    0 ≤ gainOnSubspace S M :=
  Real.sInf_nonneg fun _ ⟨_, _, _, hr⟩ =>
    hr.symm ▸ div_nonneg (norm_nonneg _) (norm_nonneg _)
end SNumbers
