-- Prove2me | solution 1 for SNumbers.kolmogorovNumber_multiplicative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:01:40.193927+00:00
-- url     : https://prove2.me/submissions/532c0544-3940-4dbb-a519-c4f21da318bd

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
public import Theorems.Thm_SNumbers_deviationFromSubspace_nonneg
public import Theorems.Thm_SNumbers_kolmogorovSet_nonempty
public import Theorems.Thm_SNumbers_kolmogorovNumber_le_deviation
public import Theorems.Thm_SNumbers_kolmogorovNumber_nonneg
public import Theorems.Thm_SNumbers_deviationFromSubspace_comp_sup_map_le

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
theorem _root_.solution (S : Y →L[𝕜] Z) (T : X →L[𝕜] Y) (n m : ℕ) :
    kolmogorovNumber (S.comp T) (n + m) ≤ kolmogorovNumber S n * kolmogorovNumber T m := by
  -- one admissible subspace for each operator
  have hkey : ∀ V : Submodule 𝕜 Z, Module.rank 𝕜 V ≤ (n : Cardinal) →
      ∀ U : Submodule 𝕜 Y, Module.rank 𝕜 U ≤ (m : Cardinal) →
      kolmogorovNumber (S.comp T) (n + m) ≤
        deviationFromSubspace S V * deviationFromSubspace T U := by
    intro V hV U hU
    have h_rank : Module.rank 𝕜 ↥(V ⊔ U.map (S : Y →ₗ[𝕜] Z)) ≤
        ((n + m : ℕ) : Cardinal) := by
      rw [Nat.cast_add]
      exact (Submodule.rank_add_le_rank_add_rank _ _).trans
        (add_le_add hV ((rank_map_le _ _).trans hU))
    exact (kolmogorovNumber_le_deviation h_rank).trans
      (deviationFromSubspace_comp_sup_map_le S T V U)
  -- For fixed `V`, take the infimum over `U`, pulling `‖π_V ∘ S‖ ≥ 0` inside it.
  have h1 : ∀ V : Submodule 𝕜 Z, Module.rank 𝕜 V ≤ (n : Cardinal) →
      kolmogorovNumber (S.comp T) (n + m) ≤
        deviationFromSubspace S V * kolmogorovNumber T m := by
    intro V hV
    show _ ≤ deviationFromSubspace S V • sInf (kolmogorovSet T m)
    rw [← Real.sInf_smul_of_nonneg (deviationFromSubspace_nonneg S V)]
    refine le_csInf ((kolmogorovSet_nonempty T m).image _) ?_
    rintro _ ⟨_, ⟨U, hU, rfl⟩, rfl⟩
    exact hkey V hV U hU
  -- Then take the infimum over `V`, pulling `d_m(T) ≥ 0` inside it.
  rw [mul_comm]
  show _ ≤ kolmogorovNumber T m • sInf (kolmogorovSet S n)
  rw [← Real.sInf_smul_of_nonneg (kolmogorovNumber_nonneg T m)]
  refine le_csInf ((kolmogorovSet_nonempty S n).image _) ?_
  rintro _ ⟨_, ⟨V, hV, rfl⟩, rfl⟩
  show _ ≤ kolmogorovNumber T m * deviationFromSubspace S V
  rw [mul_comm]
  exact h1 V hV
end SNumbers
