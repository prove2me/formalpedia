-- Prove2me | solution 1 for SNumbers.gelfandSet_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:54:18.294846+00:00
-- url     : https://prove2.me/submissions/390ac6fe-a0c8-4a12-8cae-a813f76a8d12

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
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) :
    (gelfandSet S n).Nonempty := by
  refine ⟨_, ⊤, ?_, ?_, rfl⟩
  · -- `(⊤ : Submodule 𝕜 X) : Set X` is `Set.univ`, which is closed.
    rw [Submodule.top_coe]; exact isClosed_univ
  · -- `rank (X ⧸ ⊤) = 0` since `X ⧸ ⊤` is subsingleton.
    have h0 : Module.rank 𝕜 (X ⧸ (⊤ : Submodule 𝕜 X)) = 0 :=
      rank_zero_iff.mpr inferInstance
    rw [h0]; exact bot_le
end SNumbers
