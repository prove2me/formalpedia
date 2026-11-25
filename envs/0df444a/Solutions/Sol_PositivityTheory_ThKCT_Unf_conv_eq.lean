-- Prove2me | solution 1 for PositivityTheory.ThKCT.Unf.conv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:00:33.739156+00:00
-- url     : https://prove2.me/submissions/b6b9569a-887d-490d-bcd0-6449186cbbda

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_RightOfCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Unf
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (ν : Measure G) [ν.IsHaarMeasure] (m : Measure G) [SFinite m] {P : Set G} {K : Subgroup G}
omit [T2Space G]
namespace PositivityTheory.ThKCT.Unf
theorem _root_.solution (hP : ∀ p ∈ P, m.map (p * ·) = m) (hPK : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) {f b : G → ℝ≥0∞}
    (hf : Measurable f) (hb : Measurable b) (hbK : ∀ g, ∀ k ∈ K, b (g * k) = b g) :
    ∫⁻ g, b g * ∫⁻ x, f (x * g) ∂m ∂ν = (∫⁻ x, b x⁻¹ ∂m) * ∫⁻ g, f g ∂ν := by
  have c : ∀ g, ∫⁻ x, b (x⁻¹ * g) ∂m = ∫⁻ x, b x⁻¹ ∂m := fun g => by
    obtain ⟨p, hp, k, hk, rfl⟩ := hPK g
    conv_lhs => rw [← hP p hp]
    rw [lintegral_map (by fun_prop) (measurable_const_mul p)]
    simp [mul_assoc, hbK _ k hk]
  calc _ = ∫⁻ g, ∫⁻ x, b g * f (x * g) ∂m ∂ν := by
        refine lintegral_congr fun g => (lintegral_const_mul _ (by fun_prop)).symm
    _ = ∫⁻ x, ∫⁻ g, b g * f (x * g) ∂ν ∂m := lintegral_lintegral_swap (Measurable.aemeasurable (by fun_prop))
    _ = ∫⁻ x, ∫⁻ g, b (x⁻¹ * g) * f g ∂ν ∂m := by
        refine lintegral_congr fun x => ?_
        rw [← lintegral_mul_left_eq_self _ x⁻¹]
        simp
    _ = ∫⁻ g, ∫⁻ x, b (x⁻¹ * g) * f g ∂m ∂ν := (lintegral_lintegral_swap (Measurable.aemeasurable (by fun_prop))).symm
    _ = _ := by
        rw [← lintegral_const_mul _ hf]
        refine lintegral_congr fun g => ?_
        rw [lintegral_mul_const _ (by fun_prop), c]
end PositivityTheory.ThKCT.Unf
