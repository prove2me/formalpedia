-- Prove2me | solution 1 for SNumbers.le_gelfandNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:56:20.06707+00:00
-- url     : https://prove2.me/submissions/cd3259a8-6687-4035-a775-f310e103966e

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
public import Theorems.Thm_SNumbers_gelfandSet_nonempty

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
theorem _root_.solution {S : X →L[𝕜] Y} {n : ℕ} {f : ℝ}
    (h : ∀ M : Submodule 𝕜 X, IsClosed (M : Set X) →
        Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal) → f ≤ deviationFromRestriction S M) :
    f ≤ gelfandNumber S n :=
  le_csInf (gelfandSet_nonempty S n) <| by
    rintro _ ⟨M, hM_closed, hM_rank, rfl⟩; exact h M hM_closed hM_rank
end SNumbers
