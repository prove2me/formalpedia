-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.chT_plateau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:13:47.975607+00:00
-- url     : https://prove2.me/submissions/1a99fd0a-35ef-4f42-801a-6c6d15353671

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {n : ℕ} (K U : Set (V n)) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ρ : V n → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ U ∧
      ∃ O : Set (V n), IsOpen O ∧ K ⊆ O ∧ ∀ y ∈ O, ρ y = 1 := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨t, htK, htf, hcov⟩ := hK.finite_cover_balls (e := δ / 3) (by positivity)
  let bx : ∀ x : V n, ContDiffBump x := fun x => ⟨δ / 3, 2 * δ / 3, by positivity, by linarith⟩
  let ψ : V n → ℝ := fun y => ∑ x ∈ htf.toFinset, bx x y
  let ρ : V n → ℝ := fun y => Real.smoothTransition (ψ y)
  have hψd : ContDiff ℝ ∞ ψ := ContDiff.sum fun x _ => (bx x).contDiff
  have hρd : ContDiff ℝ ∞ ρ := Real.smoothTransition.contDiff.comp hψd
  have hsuppψ : ∀ y, ψ y ≠ 0 → y ∈ Metric.cthickening (2 * δ / 3) K := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
    have hb : y ∈ Metric.ball x (bx x).rOut := by rw [← (bx x).support_eq]; exact hxy
    exact Metric.thickening_subset_cthickening _ _
      (Metric.ball_subset_thickening (htK (htf.mem_toFinset.1 hx)) _ hb)
  have hsuppρ : ∀ y, y ∉ Metric.cthickening (2 * δ / 3) K → ρ y = 0 := by
    intro y hy
    have : ψ y = 0 := by by_contra h; exact hy (hsuppψ y h)
    simp only [ρ, this, Real.smoothTransition.zero]
  have hts : tsupport ρ ⊆ Metric.cthickening (2 * δ / 3) K :=
    closure_minimal (fun y hy => by by_contra h; exact hy (hsuppρ y h)) Metric.isClosed_cthickening
  refine ⟨ρ, hρd, HasCompactSupport.intro hK.cthickening hsuppρ,
    hts.trans ((Metric.cthickening_mono (by linarith) K).trans hδU),
    ⋃ x ∈ t, Metric.ball x (δ / 3), isOpen_biUnion fun _ _ => Metric.isOpen_ball, hcov, ?_⟩
  intro y hy
  simp only [Set.mem_iUnion] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  have h1 : bx x y = 1 := (bx x).one_of_mem_closedBall (Metric.ball_subset_closedBall hxy)
  have h2 : 1 ≤ ψ y := by
    calc (1 : ℝ) = bx x y := h1.symm
      _ ≤ ψ y := Finset.single_le_sum (f := fun x' => bx x' y) (fun x' _ => (bx x').nonneg)
          (htf.mem_toFinset.2 hx)
  exact Real.smoothTransition.one_of_one_le h2
end ReciprocityTheory.L2DbarEstimates.F
