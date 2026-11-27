-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.avg_fd_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:25:53.185934+00:00
-- url     : https://prove2.me/submissions/38c65e4a-f8c3-4b95-9e4c-733f919778b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CubeIcoMeas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {ι κ₁ κ₂ : Type} [Fintype ι] [Fintype κ₁] [Fintype κ₂]
    (B₁ : Module.Basis κ₁ ℝ (EuclideanSpace ℂ ι)) (B₂ : Module.Basis κ₂ ℝ (EuclideanSpace ℂ ι))
    (h : Submodule.span ℤ (Set.range B₁) = Submodule.span ℤ (Set.range B₂))
    (f : EuclideanSpace ℂ ι → ℝ)
    (hf : ∀ γ ∈ Submodule.span ℤ (Set.range B₁), ∀ v, f (γ + v) = f v) :
    ⨍ v in ZSpan.fundamentalDomain B₁, f v = ⨍ v in ZSpan.fundamentalDomain B₂, f v := by
  haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range B₁)) (EuclideanSpace ℂ ι) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : EuclideanSpace ℂ ι) s⟩
  have h1 := ZSpan.isAddFundamentalDomain B₁ (volume : Measure (EuclideanSpace ℂ ι))
  have h2 := ZSpan.isAddFundamentalDomain B₂ (volume : Measure (EuclideanSpace ℂ ι))
  rw [← h] at h2
  have hinv : ∀ (g : Submodule.span ℤ (Set.range B₁)) (x : EuclideanSpace ℂ ι), f (g +ᵥ x) = f x :=
    fun g x => hf g g.2 x
  rw [setAverage_eq, setAverage_eq, h1.setIntegral_eq h2 hinv]
  simp only [Measure.real, h1.measure_eq h2]
end ReciprocityTheory.ChartRestriction.G.I2
