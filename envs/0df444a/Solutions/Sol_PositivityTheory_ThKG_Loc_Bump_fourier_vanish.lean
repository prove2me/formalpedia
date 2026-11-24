-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.fourier_vanish
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:48.594874+00:00
-- url     : https://prove2.me/submissions/c3c2b4ef-b1f7-4010-85c6-d1f70fdb5c29

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_norm_ch
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_continuous_ch
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_exists_density

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
theorem _root_.solution {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] (π : Ω → X) (hπ : Measurable π) (g : Ω → ℂ)
    (hg : Integrable g μ) (h : ∀ η, ∫ p, ch ⟪η, π p⟫ * g p ∂μ = 0) (φ : 𝓢(X, ℂ)) : ∫ p, φ (π p) * g p ∂μ = 0 := by
  obtain ⟨a, ha⟩ := exists_density φ
  have hi : Integrable (fun q : Ω × X => ch ⟪q.2, π q.1⟫ * (g q.1 * a q.2)) (μ.prod volume) := by
    refine (hg.mul_prod a.integrable).bdd_mul (c := 1) ?_ (Eventually.of_forall fun q => (norm_ch _).le)
    exact (continuous_ch.measurable.comp (measurable_snd.inner (hπ.comp measurable_fst))).aestronglyMeasurable
  calc ∫ p, φ (π p) * g p ∂μ = ∫ p, ∫ η, ch ⟪η, π p⟫ * (g p * a η) ∂volume ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only [ha]
        rw [← integral_mul_const]
        congr 1; funext η; ring
    _ = ∫ η, ∫ p, ch ⟪η, π p⟫ * (g p * a η) ∂μ := integral_integral_swap hi
    _ = 0 := by
        have : ∀ η, ∫ p, ch ⟪η, π p⟫ * (g p * a η) ∂μ = 0 := fun η => by
          simp only [← mul_assoc]
          rw [integral_mul_const, h, zero_mul]
        simp [this]
end PositivityTheory.ThKG.Loc.Bump
