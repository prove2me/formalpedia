-- Prove2me | solution 1 for PositivityTheory.KReal.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:24:46.267695+00:00
-- url     : https://prove2.me/submissions/4237e894-9a8e-4c95-b447-6199e275bc62

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasGl
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution {M T P : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup T] [Module ℂ T]
    [AddCommGroup P] [Module ℂ P] (φ : M →ₗ[ℂ] T) (hφ : Function.Surjective φ) (g : M →ₗ[ℂ] P)
    (h : LinearMap.ker φ ≤ LinearMap.ker g) : ∃ π : T →ₗ[ℂ] P, ∀ m, π (φ m) = g m := by
  refine ⟨((LinearMap.ker φ).liftQ g h) ∘ₗ (φ.quotKerEquivOfSurjective hφ).symm.toLinearMap, fun m => ?_⟩
  have e : (φ.quotKerEquivOfSurjective hφ).symm (φ m) = Submodule.Quotient.mk m := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e, Submodule.liftQ_apply]
end PositivityTheory.KReal
