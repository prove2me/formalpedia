-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.Bump.zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:58.940805+00:00
-- url     : https://prove2.me/submissions/ce2b9ed7-2e1c-408e-864d-b4bf0c44cc91

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Two
open MeasureTheory Topology Filter
open scoped Pointwise
variable {G X : Type} [Group G] [TopologicalSpace G]
variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {Γ : Subgroup G} {n : X → G} {a : G} {lam : Measure X}
  [IsProbabilityMeasure lam] {l : ℂ} {φ c : G → ℂ} {V : Set G} {η : G → ℝ} (μ : Measure G) [μ.IsHaarMeasure]
namespace PositivityTheory.ThKEnd.Two
namespace Bump
theorem _root_.solution (D : G → ℂ) (hD : Continuous D) (g : G) (h : ∀ V ∈ 𝓝 (1 : G), ∃ η, Bump V η ∧ conv μ η D g = 0) : D g = 0 := by
  by_contra h0
  have hc : Continuous fun y => (D (g * y) / D g).re := by fun_prop
  obtain ⟨η, hη, e⟩ := h {y | 0 < (D (g * y) / D g).re} ((isOpen_lt continuous_const hc).mem_nhds (by simp [h0]))
  have hi := (hη.int μ hD g).div_const (D g)
  have h1 : ∫ y, (D (g * y) / D g).re * η y ∂μ = 0 := by
    have := congrArg (fun z => (z / D g).re) e
    simp only [conv, zero_div, Complex.zero_re] at this
    rw [← integral_div, ← RCLike.re_to_complex, ← integral_re hi] at this
    rw [← this]
    congr 1
    funext y
    rw [mul_div_right_comm]
    simp
  have := hη.cont
  refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (by fun_prop) hη.cpt.mul_left (fun y => ?_)
    (by simp [h0, hη.one])).ne' h1
  by_cases hy : y ∈ tsupport η
  · exact mul_nonneg (hη.sub hy).le (hη.nonneg y)
  · simp [image_eq_zero_of_notMem_tsupport hy]
end Bump
end PositivityTheory.ThKEnd.Two
