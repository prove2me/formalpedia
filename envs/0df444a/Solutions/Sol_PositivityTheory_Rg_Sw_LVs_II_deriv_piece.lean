-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.deriv_piece
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:29.548839+00:00
-- url     : https://prove2.me/submissions/466137ee-eb06-48b9-8ee1-85dc8b0fc2e7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetOneAddSmulSingleSame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.II
theorem _root_.solution (Θ : M2 n → ℂ) (x : M2 n) (hΘ : DifferentiableAt ℂ Θ x)
    (γ : ℝ → M2 n) (Y : M2 n) (hγ : HasDerivAt γ Y 0) (hγ0 : γ 0 = 1)
    (f : ℝ → ℂ) (r : ℂ) (hf : HasDerivAt f r 0)
    (hlaw : ∀ᶠ t in 𝓝 (0 : ℝ), Θ (γ t * x) = f t * Θ x) :
    fderiv ℂ Θ x (Y * x) = r * Θ x := by
  have h1 : HasDerivAt (fun t => γ t * x) (Y * x) 0 := by
    have := (rmulL x).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ
    exact this
  have hx : γ 0 * x = x := by simp [hγ0]
  have hF : HasFDerivAt Θ ((fderiv ℂ Θ x).restrictScalars ℝ) (γ 0 * x) := by
    rw [hx]; exact hΘ.hasFDerivAt.restrictScalars ℝ
  have h2 : HasDerivAt (fun t => Θ (γ t * x)) (fderiv ℂ Θ x (Y * x)) 0 := by
    have := hF.comp_hasDerivAt (0 : ℝ) h1
    exact this
  have h3 : HasDerivAt (fun t => Θ (γ t * x)) (r * Θ x) 0 :=
    (hf.mul_const (Θ x)).congr_of_eventuallyEq hlaw
  exact h2.unique h3
end PositivityTheory.Rg.Sw.LVs.II
