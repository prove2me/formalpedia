-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.coincide_null
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:00.275924+00:00
-- url     : https://prove2.me/submissions/67baa9f7-f8e6-43c9-9dc6-67e3ff6dd47b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterOsgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetB
import Theorems.Thm_ReciprocityTheory_AnForm_volume_zero_set_of_analyticOnNhd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Metric Filter Topology
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (hA : OsgoodStatement) {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {c : Fin e → ℂ} {r : ℝ}
    {G G' : (Fin e → ℂ) → ((k : K) → ι k) → ℂ} (hG : G ∈ secSet P Ψ (ball c r))
    (hG' : G' ∈ secSet P Ψ (ball c r)) (hne : G ≠ G') :
    volume {y | y ∈ ball c r ∧ G y = G' y} = 0 := by
  obtain ⟨y0, hy0⟩ : ∃ y0, G y0 ≠ G' y0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (funext hcon)
  have hy0b : y0 ∈ ball c r := by
    by_contra hb
    exact hy0 (by rw [hG.1 y0 hb, hG'.1 y0 hb])
  obtain ⟨i, hi⟩ : ∃ i, G y0 i ≠ G' y0 i := by
    by_contra hcon
    push_neg at hcon
    exact hy0 (funext hcon)
  set f : (Fin e → ℂ) → ℂ := fun y => G y i - G' y i with hf
  have hdiff : DifferentiableOn ℂ f (ball c r) := by
    have h1 : DifferentiableOn ℂ (fun y => G y i) (ball c r) := fun y hy =>
      (differentiableWithinAt_pi.1 (hG.2.1 y hy)) i
    have h2 : DifferentiableOn ℂ (fun y => G' y i) (ball c r) := fun y hy =>
      (differentiableWithinAt_pi.1 (hG'.2.1 y hy)) i
    exact h1.sub h2
  have han : AnalyticOnNhd ℂ f (ball c r) := hA e (ball c r) f isOpen_ball hdiff
  have hnull := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_ball (convex_ball c r).isPreconnected han
    ⟨y0, hy0b, sub_ne_zero.2 hi⟩
  refine measure_mono_null ?_ hnull
  intro y hy
  exact ⟨hy.1, by simp [f, hy.2]⟩
end ReciprocityTheory.ChartRestriction.G.Geo
