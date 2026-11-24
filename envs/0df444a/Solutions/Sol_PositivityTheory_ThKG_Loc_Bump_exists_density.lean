-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.exists_density
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:43.950611+00:00
-- url     : https://prove2.me/submissions/85297727-b59b-4356-a58b-a3e40d0eb7ac

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped FourierTransform SchwartzMap RealInnerProductSpace
variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [MeasurableSpace X] [BorelSpace X]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution (φ : 𝓢(X, ℂ)) : ∃ a : 𝓢(X, ℂ), ∀ x, φ x = ∫ η, ch ⟪η, x⟫ * a η := by
  refine ⟨𝓕 φ, fun x => ?_⟩
  have h : (𝓕⁻ (𝓕 φ) : 𝓢(X, ℂ)) = φ := FourierTransform.fourierInv_fourier_eq φ
  conv_lhs => rw [← h]
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only [ch, smul_eq_mul]
  congr 2
  push_cast; ring
end PositivityTheory.ThKG.Loc.Bump
