-- Prove2me | solution 1 for SpectralRepresentation.isPositive_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:49:12.554565+00:00
-- url     : https://prove2.me/submissions/8d624c74-7bab-4048-93c7-1fe4c3c2b624

module
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Definitions.Def_BasicResults_Spectral_MonotoneConvergence
public import Theorems.Thm_SpectralRepresentation_isSymmetric_of_tendsto

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
    (hpos : ∀ n, (T n).IsPositive)
    (hE : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (E x))) : E.IsPositive := by
  refine ⟨isSymmetric_of_tendsto (fun n => (hpos n).1) hE, fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  refine ge_of_tendsto' ((RCLike.continuous_re.tendsto _).comp ((hE x).inner tendsto_const_nhds))
    fun n => ?_
  have := (hpos n).2 x
  rwa [ContinuousLinearMap.reApplyInnerSelf_apply] at this
end SpectralRepresentation
