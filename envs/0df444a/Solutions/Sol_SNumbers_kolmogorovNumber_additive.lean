-- Prove2me | solution 1 for SNumbers.kolmogorovNumber_additive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:42:34.553577+00:00
-- url     : https://prove2.me/submissions/464f159d-9de4-4146-951f-853614c5d5e9

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
public import Theorems.Thm_SNumbers_kolmogorovNumber_le_deviation
public import Theorems.Thm_SNumbers_le_kolmogorovNumber
public import Theorems.Thm_SNumbers_deviationFromSubspace_anti
public import Theorems.Thm_SNumbers_deviationFromSubspace_add_le

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
    kolmogorovNumber (S + T) (n + m) ≤ kolmogorovNumber S n + kolmogorovNumber T m := by
  -- one admissible subspace for each operator
  have hkey : ∀ V : Submodule 𝕜 Y, Module.rank 𝕜 V ≤ (n : Cardinal) →
      ∀ U : Submodule 𝕜 Y, Module.rank 𝕜 U ≤ (m : Cardinal) →
      kolmogorovNumber (S + T) (n + m) ≤
        deviationFromSubspace S V + deviationFromSubspace T U := by
    intro V hV U hU
    have h_rank : Module.rank 𝕜 ↥(V ⊔ U) ≤ ((n + m : ℕ) : Cardinal) := by
      rw [Nat.cast_add]
      exact (Submodule.rank_add_le_rank_add_rank V U).trans (add_le_add hV hU)
    calc kolmogorovNumber (S + T) (n + m)
        ≤ deviationFromSubspace (S + T) (V ⊔ U) := kolmogorovNumber_le_deviation h_rank
      _ ≤ deviationFromSubspace S (V ⊔ U) + deviationFromSubspace T (V ⊔ U) :=
          deviationFromSubspace_add_le S T _
      _ ≤ deviationFromSubspace S V + deviationFromSubspace T U :=
          add_le_add (deviationFromSubspace_anti S le_sup_left)
            (deviationFromSubspace_anti T le_sup_right)
  -- infimum over `V`, then over `U`
  rw [← sub_le_iff_le_add]
  refine le_kolmogorovNumber fun V hV => ?_
  rw [sub_le_comm]
  refine le_kolmogorovNumber fun U hU => ?_
  linarith [hkey V hV U hU]
end SNumbers
