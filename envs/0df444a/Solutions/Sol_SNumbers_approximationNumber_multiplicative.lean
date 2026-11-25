-- Prove2me | solution 1 for SNumbers.approximationNumber_multiplicative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:01:32.945886+00:00
-- url     : https://prove2.me/submissions/a101c1a4-21ee-4692-882e-0128087d8f75

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
public import Theorems.Thm_SNumbers_approximationSet_nonempty
public import Theorems.Thm_SNumbers_approximationNumber_nonneg
public import Theorems.Thm_SNumbers_approximationNumber_comp_le_norm_sub_mul

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
    approximationNumber (S.comp T) (n + m) ≤
      approximationNumber S n * approximationNumber T m := by
  -- For a fixed approximant `L` of `S`, take the infimum over the approximants `K` of `T`,
  -- pulling the non-negative factor `‖S - L‖` inside it.
  have h1 : ∀ L : Y →L[𝕜] Z, L.rank ≤ (n : Cardinal) →
      approximationNumber (S.comp T) (n + m) ≤ ‖S - L‖ * approximationNumber T m := by
    intro L hL
    show _ ≤ ‖S - L‖ • sInf (approximationSet T m)
    rw [← Real.sInf_smul_of_nonneg (norm_nonneg _)]
    refine le_csInf ((approximationSet_nonempty T m).image _) ?_
    rintro _ ⟨_, ⟨K, hK, rfl⟩, rfl⟩
    exact approximationNumber_comp_le_norm_sub_mul hL hK
  -- Then take the infimum over `L`, pulling the factor `a_m(T) ≥ 0` inside it.
  rw [mul_comm]
  show _ ≤ approximationNumber T m • sInf (approximationSet S n)
  rw [← Real.sInf_smul_of_nonneg (approximationNumber_nonneg T m)]
  refine le_csInf ((approximationSet_nonempty S n).image _) ?_
  rintro _ ⟨_, ⟨L, hL, rfl⟩, rfl⟩
  show _ ≤ approximationNumber T m * ‖S - L‖
  rw [mul_comm]
  exact h1 L hL
end SNumbers
