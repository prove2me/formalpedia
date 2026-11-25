-- Prove2me | solution 1 for SNumbers.sn_eq_singularValues_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:23:38.604804+00:00
-- url     : https://prove2.me/submissions/65ba14df-594e-45b9-8043-a982fa45816b

module
public import Definitions.Def_SNumbers_Uniqueness
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_SingularValuesFinDim
public import Theorems.Thm_SNumbers_project_singularValues_eq
public import Theorems.Thm_SNumbers_allSNumbers_eq_on_HilbertSpace


set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [FiniteDimensional 𝕜 H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [FiniteDimensional 𝕜 H₂]
variable [Nontrivial H₁] [Nontrivial H₂]
omit [Nontrivial H₁] [Nontrivial H₂]
namespace SNumbers
theorem _root_.solution {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : H₁ →L[𝕜] H₂) (n : ℕ) :
    s S n = (S : H₁ →ₗ[𝕜] H₂).singularValues n := by
  have : CompleteSpace H₁ := FiniteDimensional.complete 𝕜 H₁
  have : CompleteSpace H₂ := FiniteDimensional.complete 𝕜 H₂
  rw [allSNumbers_eq_on_HilbertSpace hs S n, ← project_singularValues_eq S n]
end SNumbers
