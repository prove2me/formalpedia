-- Prove2me | solution 1 for SpectralRepresentation.isSymmetric_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:41:38.120772+00:00
-- url     : https://prove2.me/submissions/3538bac8-bd24-4bf9-9d89-04578afd41b9

module
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Definitions.Def_BasicResults_Spectral_MonotoneConvergence

set_option autoImplicit true
@[expose] public section
public section
open ContinuousLinearMap RCLike
open scoped InnerProductSpace
open SpectralRepresentation
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Nontrivial H]
open Filter Topology
omit [CompleteSpace H] [Nontrivial H]
namespace SpectralRepresentation
theorem _root_.solution {T : ℕ → H →L[ℂ] H} {E : H →L[ℂ] H}
    (hsymm : ∀ n, (T n : H →ₗ[ℂ] H).IsSymmetric)
    (hE : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (E x))) : (E : H →ₗ[ℂ] H).IsSymmetric := by
  intro x y
  refine tendsto_nhds_unique ((hE x).inner tendsto_const_nhds) ?_
  have heq : (fun n => ⟪T n x, y⟫_ℂ) = (fun n => ⟪x, T n y⟫_ℂ) := funext fun n => hsymm n x y
  rw [heq]
  exact tendsto_const_nhds.inner (hE y)
end SpectralRepresentation
