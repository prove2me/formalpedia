-- Prove2me | solution 1 for SNumbers.gainOnSubspace_le_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:51:47.116801+00:00
-- url     : https://prove2.me/submissions/6afc41e8-20bc-449b-bb4b-7bb09faa297d

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Definitions.Def_SNumbers_Bernstein
section
@[expose] public section
universe u
open scoped Cardinal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
private lemma gainSet_bddBelow (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    BddBelow {r : ℝ | ∃ x : X, x ∈ M ∧ x ≠ 0 ∧ r = ‖S x‖ / ‖x‖} :=
  ⟨0, by rintro _ ⟨_, _, _, rfl⟩; exact div_nonneg (norm_nonneg _) (norm_nonneg _)⟩
end SNumbers
end
end

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
theorem _root_.solution {S : X →L[𝕜] Y} {M : Submodule 𝕜 X} {x : X}
    (hx_mem : x ∈ M) (hx_ne : x ≠ 0) :
    gainOnSubspace S M ≤ ‖S x‖ / ‖x‖ :=
  csInf_le (gainSet_bddBelow S M) ⟨x, hx_mem, hx_ne, rfl⟩
end SNumbers
