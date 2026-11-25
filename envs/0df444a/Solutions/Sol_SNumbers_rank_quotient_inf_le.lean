-- Prove2me | solution 1 for SNumbers.rank_quotient_inf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:56:42.325994+00:00
-- url     : https://prove2.me/submissions/9982dd95-754b-47f5-b4aa-36765a27dfe5

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand

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
theorem _root_.solution (M N : Submodule 𝕜 X) :
    Module.rank 𝕜 (X ⧸ (M ⊓ N)) ≤ Module.rank 𝕜 (X ⧸ M) + Module.rank 𝕜 (X ⧸ N) := by
  set g : X →ₗ[𝕜] (X ⧸ M) × (X ⧸ N) := LinearMap.prod M.mkQ N.mkQ with hg_def
  have h_ker : LinearMap.ker g = M ⊓ N := by
    rw [hg_def, LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]
  calc Module.rank 𝕜 (X ⧸ (M ⊓ N))
      = Module.rank 𝕜 (X ⧸ LinearMap.ker g) := by rw [h_ker]
    _ = Module.rank 𝕜 (LinearMap.range g) :=
        (LinearMap.quotKerEquivRange g).rank_eq
    _ ≤ Module.rank 𝕜 ((X ⧸ M) × (X ⧸ N)) :=
        (LinearMap.range g).rank_le
    _ = Module.rank 𝕜 (X ⧸ M) + Module.rank 𝕜 (X ⧸ N) := rank_prod'
end SNumbers
