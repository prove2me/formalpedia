-- Prove2me | solution 1 for SpectralRepresentation.commute_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:56.613263+00:00
-- url     : https://prove2.me/submissions/c676d23e-33fa-4688-9370-23e9fef12ad0

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
theorem _root_.solution {T : ℕ → H →L[ℂ] H} {E P : H →L[ℂ] H}
    (hcomm : ∀ n, (T n).comp P = P.comp (T n))
    (hE : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (E x))) : E.comp P = P.comp E := by
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  refine tendsto_nhds_unique (hE (P x)) ?_
  have heq : (fun n => T n (P x)) = (fun n => P (T n x)) := funext fun n => by
    rw [← ContinuousLinearMap.comp_apply, hcomm n, ContinuousLinearMap.comp_apply]
  rw [heq]
  exact (P.continuous.tendsto (E x)).comp (hE x)
end SpectralRepresentation
