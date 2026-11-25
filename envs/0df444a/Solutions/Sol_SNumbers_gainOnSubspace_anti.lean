-- Prove2me | solution 1 for SNumbers.gainOnSubspace_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:01.700805+00:00
-- url     : https://prove2.me/submissions/c964dcd9-b406-494f-ada7-17915ee9f418

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
private lemma gainSet_nonempty_of_ne_bot (S : X →L[𝕜] Y) {M : Submodule 𝕜 X}
    (hM : M ≠ ⊥) :
    {r : ℝ | ∃ x : X, x ∈ M ∧ x ≠ 0 ∧ r = ‖S x‖ / ‖x‖}.Nonempty := by
  obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
  exact ⟨_, x, hx_mem, hx_ne, rfl⟩
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
theorem _root_.solution {S : X →L[𝕜] Y} {M M' : Submodule 𝕜 X}
    (h_le : M' ≤ M) (hM' : M' ≠ ⊥) :
    gainOnSubspace S M ≤ gainOnSubspace S M' := by
  refine csInf_le_csInf (gainSet_bddBelow S M)
    (gainSet_nonempty_of_ne_bot S hM') ?_
  rintro _ ⟨x, hx_mem', hx_ne, rfl⟩
  exact ⟨x, h_le hx_mem', hx_ne, rfl⟩
end SNumbers
