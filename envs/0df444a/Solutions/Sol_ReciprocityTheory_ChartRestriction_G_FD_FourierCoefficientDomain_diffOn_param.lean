-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.diffOn_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:14.011314+00:00
-- url     : https://prove2.me/submissions/a59c4e0a-5733-41d5-9334-4b1d4a342440

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
import Definitions.Def_Lemmata_GeneralBFactBisForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientDomain_norm_fderiv_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory Metric Set Filter
open scoped ComplexConjugate Topology
noncomputable section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain
theorem _root_.solution {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKm : MeasurableSet K)
    (A : (Fin n → ℝ) → F →L[ℂ] F) (hA : Continuous A) {U : Set F} (hU : IsOpen U)
    (hAU : ∀ t ∈ K, ∀ x ∈ U, A t x ∈ U) (G : F → ℂ) (hG : DifferentiableOn ℂ G U)
    (e : (Fin n → ℝ) → ℂ) (he : Continuous e) :
    DifferentiableOn ℂ (fun x => ∫ t in K, G (A t x) * e t) U := by
  intro x0 hx0
  have hcA : ∀ x, Continuous fun t => A t x := fun x => hA.clm_apply continuous_const
  set K0 := (fun t => A t x0) '' K with hK0def
  have hK0 : IsCompact K0 := hK.image (hcA x0)
  have hK0U : K0 ⊆ U := by rintro _ ⟨t, ht, rfl⟩; exact hAU t ht x0 hx0
  obtain ⟨δ, hδ, hδU⟩ := hK0.exists_cthickening_subset_open hU hK0U
  have hK1 : IsCompact (cthickening δ K0) := hK0.cthickening
  obtain ⟨C, hC⟩ := hK1.exists_bound_of_continuousOn (hG.continuousOn.mono hδU)
  obtain ⟨Am, hAm⟩ := hK.exists_bound_of_continuousOn hA.continuousOn
  obtain ⟨Me, hMe⟩ := hK.exists_bound_of_continuousOn he.continuousOn
  set A1 := max Am 1 with hA1def
  have hA1 : 0 < A1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set ε := δ / 2 / A1 with hεdef
  have hε : 0 < ε := by positivity
  have hnear : ∀ t ∈ K, ∀ x ∈ ball x0 ε, closedBall (A t x) (δ / 2) ⊆ cthickening δ K0 := by
    intro t ht x hx z hz
    have hx' : ‖x - x0‖ < ε := by rw [← dist_eq_norm]; exact hx
    have h1 : dist (A t x) (A t x0) ≤ δ / 2 := by
      rw [dist_eq_norm, ← map_sub]
      calc ‖A t (x - x0)‖ ≤ ‖A t‖ * ‖x - x0‖ := (A t).le_opNorm _
        _ ≤ A1 * ε := mul_le_mul (le_trans (hAm t ht) (le_max_left _ _)) hx'.le (norm_nonneg _) hA1.le
        _ = δ / 2 := by rw [hεdef]; field_simp
    have h2 : dist z (A t x0) ≤ δ := by
      linarith [dist_triangle z (A t x) (A t x0), mem_closedBall.1 hz]
    exact mem_cthickening_of_dist_le z (A t x0) δ K0 ⟨t, ht, rfl⟩ h2
  have hin : ∀ t ∈ K, ∀ x ∈ ball x0 ε, A t x ∈ U := fun t ht x hx =>
    hδU (hnear t ht x hx (mem_closedBall_self (by positivity)))
  have hfd : ∀ t ∈ K, ∀ x ∈ ball x0 ε, ‖fderiv ℂ G (A t x)‖ ≤ C / (δ / 2) := fun t ht x hx =>
    norm_fderiv_le hU hG (by positivity) ((hnear t ht x hx).trans hδU)
      (fun z hz => hC z (hnear t ht x hx hz))
  have hball : ball x0 ε ∈ 𝓝 x0 := ball_mem_nhds x0 hε
  have hcont : ∀ x ∈ ball x0 ε, ContinuousOn (fun t => G (A t x) * e t) K := fun x hx =>
    (hG.continuousOn.comp (hcA x).continuousOn (fun t ht => hin t ht x hx)).mul he.continuousOn
  have hfin : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have m1 : Measurable fun t => fderiv ℂ G (A t x0) := (measurable_fderiv ℂ G).comp (hcA x0).measurable
  have m2 : Measurable fun t => (fderiv ℂ G (A t x0)).comp (A t) :=
    (isBoundedBilinearMap_comp.continuous.measurable).comp (m1.prodMk hA.measurable)
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict K)
    (F := fun x t => G (A t x) * e t)
    (F' := fun x t => e t • (fderiv ℂ G (A t x)).comp (A t))
    (bound := fun _ => Me * (C / (δ / 2) * A1)) hball
    (by filter_upwards [hball] with x hx; exact (hcont x hx).aestronglyMeasurable hKm)
    ((hcont x0 (mem_ball_self hε)).integrableOn_compact hK)
    ((he.measurable.smul m2).aestronglyMeasurable)
    ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun t ht x hx => by
      calc ‖e t • (fderiv ℂ G (A t x)).comp (A t)‖
          = ‖e t‖ * ‖(fderiv ℂ G (A t x)).comp (A t)‖ := norm_smul _ _
        _ ≤ Me * (C / (δ / 2) * A1) := by
          refine mul_le_mul (hMe t ht) ?_ (norm_nonneg _) (le_trans (norm_nonneg _) (hMe t ht))
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hfd t ht x hx)
            (le_trans (hAm t ht) (le_max_left _ _)) (norm_nonneg _)
            (le_trans (norm_nonneg _) (hfd t ht x hx)))))
    (integrable_const _)
    ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun t ht x hx => by
      have h1 : HasFDerivAt G (fderiv ℂ G (A t x)) (A t x) :=
        (hG.differentiableAt (hU.mem_nhds (hin t ht x hx))).hasFDerivAt
      exact (h1.comp x (A t).hasFDerivAt).mul_const (e t)))
  exact key.differentiableAt.differentiableWithinAt
end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain
