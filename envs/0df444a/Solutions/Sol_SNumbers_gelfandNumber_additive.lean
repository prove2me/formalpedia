-- Prove2me | solution 1 for SNumbers.gelfandNumber_additive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:32:54.20551+00:00
-- url     : https://prove2.me/submissions/83c5a994-fb5c-4226-85ae-5e152bb05256

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
public import Theorems.Thm_SNumbers_gelfandNumber_le_deviation
public import Theorems.Thm_SNumbers_le_gelfandNumber
public import Theorems.Thm_SNumbers_deviationFromRestriction_mono
public import Theorems.Thm_SNumbers_deviationFromRestriction_add_le
public import Theorems.Thm_SNumbers_rank_quotient_inf_le

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
theorem _root_.solution (S T : X →L[𝕜] Y) (n m : ℕ) :
    gelfandNumber (S + T) (n + m) ≤ gelfandNumber S n + gelfandNumber T m := by
  -- one admissible subspace for each operator
  have hkey : ∀ M : Submodule 𝕜 X, IsClosed (M : Set X) →
      Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal) →
      ∀ N : Submodule 𝕜 X, IsClosed (N : Set X) →
      Module.rank 𝕜 (X ⧸ N) ≤ (m : Cardinal) →
      gelfandNumber (S + T) (n + m) ≤
        deviationFromRestriction S M + deviationFromRestriction T N := by
    intro M hM_closed hM_rank N hN_closed hN_rank
    have h_closed : IsClosed ((M ⊓ N : Submodule 𝕜 X) : Set X) := by
      rw [Submodule.coe_inf]; exact hM_closed.inter hN_closed
    have h_rank : Module.rank 𝕜 (X ⧸ (M ⊓ N)) ≤ ((n + m : ℕ) : Cardinal) := by
      rw [Nat.cast_add]
      exact (rank_quotient_inf_le M N).trans (add_le_add hM_rank hN_rank)
    calc gelfandNumber (S + T) (n + m)
        ≤ deviationFromRestriction (S + T) (M ⊓ N) :=
          gelfandNumber_le_deviation h_closed h_rank
      _ ≤ deviationFromRestriction S (M ⊓ N) + deviationFromRestriction T (M ⊓ N) :=
          deviationFromRestriction_add_le S T _
      _ ≤ deviationFromRestriction S M + deviationFromRestriction T N :=
          add_le_add (deviationFromRestriction_mono S inf_le_left)
            (deviationFromRestriction_mono T inf_le_right)
  -- infimum over `M`, then over `N`
  rw [← sub_le_iff_le_add]
  refine le_gelfandNumber fun M hM_closed hM_rank => ?_
  rw [sub_le_comm]
  refine le_gelfandNumber fun N hN_closed hN_rank => ?_
  linarith [hkey M hM_closed hM_rank N hN_closed hN_rank]
end SNumbers
