-- Prove2me | solution 1 for PI.AprimeInfG.tubeChart_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:19:22.63942+00:00
-- url     : https://prove2.me/submissions/d5278e81-b849-459d-9132-2153064c320a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_GrpTube
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_GrpChartC
import Theorems.Thm_PI_AprimeInfA_polish_of_lcsc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfG
open MeasureTheory Topology Filter Metric Set
open scoped ENNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace PI.AprimeInfG
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (ν : Measure H) {ι η : Type} [Fintype ι] [Fintype η]
    (κ : EuclideanSpace ℝ ι → G) (χ : EuclideanSpace ℝ η → H) {r0 : ℝ} (hr0 : 0 < r0)
    (hκc : ContinuousOn κ (ball 0 r0)) (hχc : ContinuousOn χ (ball 0 r0)) (hχi : InjOn χ (ball 0 r0))
    (hinj : ∀ a ∈ ball (0 : EuclideanSpace ℝ ι) r0, ∀ b ∈ ball (0 : EuclideanSpace ℝ ι) r0,
      (κ a)⁻¹ * κ b ∈ H → a = b)
    (φ : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → G) (U : Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ η))
    (D : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ)
    (hφ : ∀ A ⊆ U, MeasurableSet A → μ (φ '' A) = ∫⁻ z in A, ENNReal.ofReal (D z))
    (F : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → EuclideanSpace ℝ ι × EuclideanSpace ℝ η)
    (F' : EuclideanSpace ℝ ι × EuclideanSpace ℝ η →
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ η →L[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ η))
    (hF : ∀ p ∈ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r0, HasFDerivWithinAt F (F' p) (ball 0 r0) p)
    (hFi : InjOn F (ball 0 r0)) (hFU : F '' ball 0 r0 ⊆ U)
    (hΦ : ∀ p ∈ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r0, κ p.1 * (χ p.2 : G) = φ (F p))
    (e : EuclideanSpace ℝ η → ℝ)
    (hνH : ∀ s, 0 < s → s ≤ r0 → ν (χ '' ball 0 s) = ∫⁻ y in ball 0 s, ENNReal.ofReal (e y)) :
    TubeChart μ H ν κ χ r0 (fun p => |(F' p).det| * D (F p)) e := by
  have : (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have : PolishSpace G := PI.AprimeInfA.polish_of_lcsc G
  have hbox : ∀ ρ s, ρ ≤ r0 → s ≤ r0 →
      ball (0 : EuclideanSpace ℝ ι) ρ ×ˢ ball (0 : EuclideanSpace ℝ η) s ⊆
        ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r0 := by
    intro ρ s hρ hs p hp
    rw [mem_ball_zero_iff, Prod.norm_def]
    exact max_lt ((mem_ball_zero_iff.1 hp.1).trans_le hρ) ((mem_ball_zero_iff.1 hp.2).trans_le hs)
  have himg : ∀ ρ s, tubeS H (κ '' ball 0 ρ) (χ '' ball 0 s) =
      (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η => κ p.1 * (χ p.2 : G)) '' (ball 0 ρ ×ˢ ball 0 s) := by
    intro ρ s
    ext g
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
      exact ⟨κ x, ⟨x, hx, rfl⟩, χ y, ⟨y, hy, rfl⟩, rfl⟩
  have hΦinj : InjOn (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η => κ p.1 * (χ p.2 : G))
      (ball 0 r0 ×ˢ ball 0 r0) := by
    intro p hp q hq he
    simp only at he
    have hm : (κ p.1)⁻¹ * κ q.1 ∈ H := by
      have : (κ p.1)⁻¹ * κ q.1 = (χ p.2 : G) * (χ q.2 : G)⁻¹ := by
        calc (κ p.1)⁻¹ * κ q.1 = (κ p.1)⁻¹ * (κ q.1 * (χ q.2 : G)) * (χ q.2 : G)⁻¹ := by group
          _ = (κ p.1)⁻¹ * (κ p.1 * (χ p.2 : G)) * (χ q.2 : G)⁻¹ := by rw [he]
          _ = (χ p.2 : G) * (χ q.2 : G)⁻¹ := by group
      rw [this]
      exact H.mul_mem (χ p.2).2 (H.inv_mem (χ q.2).2)
    have h1 := hinj _ hp.1 _ hq.1 hm
    rw [h1] at he
    have h2 : (χ p.2 : G) = χ q.2 := mul_left_cancel he
    exact Prod.ext h1 (hχi hp.2 hq.2 (Subtype.ext h2))
  refine ⟨hr0, hinj, ?_, ?_, ?_, ?_, hνH⟩
  · intro s hs hsr
    exact measurableSet_ball.image_of_continuousOn_injOn (hχc.mono (ball_subset_ball hsr))
      (hχi.mono (ball_subset_ball hsr))
  · intro ρ s hρ hρr hs hsr
    rw [himg]
    have hsub : ball (0 : EuclideanSpace ℝ ι) ρ ×ˢ ball (0 : EuclideanSpace ℝ η) s ⊆ ball 0 r0 ×ˢ ball 0 r0 :=
      prod_mono (ball_subset_ball hρr) (ball_subset_ball hsr)
    have hc : ContinuousOn (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η => κ p.1 * (χ p.2 : G))
        (ball 0 ρ ×ˢ ball 0 s) :=
      (hκc.comp continuousOn_fst fun p hp => ball_subset_ball hρr hp.1).mul
        (continuous_subtype_val.comp_continuousOn (hχc.comp continuousOn_snd fun p hp => ball_subset_ball hsr hp.2))
    exact (measurableSet_ball.prod measurableSet_ball).image_of_continuousOn_injOn hc (hΦinj.mono hsub)
  · intro ρ hρ hρr
    have : PolishSpace (H : Set G) := hH.polishSpace
    have : PolishSpace H := this
    have e1 : tubeS H (κ '' ball 0 ρ) univ =
        (fun p : EuclideanSpace ℝ ι × H => κ p.1 * (p.2 : G)) '' (ball 0 ρ ×ˢ univ) := by
      ext g
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, h, -, rfl⟩
        exact ⟨(x, h), ⟨hx, mem_univ _⟩, rfl⟩
      · rintro ⟨⟨x, h⟩, ⟨hx, -⟩, rfl⟩
        exact ⟨κ x, ⟨x, hx, rfl⟩, h, mem_univ _, rfl⟩
    rw [e1]
    have hc : ContinuousOn (fun p : EuclideanSpace ℝ ι × H => κ p.1 * (p.2 : G)) (ball 0 ρ ×ˢ univ) :=
      (hκc.comp continuousOn_fst fun p hp => ball_subset_ball hρr hp.1).mul
        (continuous_subtype_val.comp continuous_snd).continuousOn
    have hi : InjOn (fun p : EuclideanSpace ℝ ι × H => κ p.1 * (p.2 : G)) (ball 0 ρ ×ˢ univ) := by
      intro p hp q hq he
      simp only at he
      have hm : (κ p.1)⁻¹ * κ q.1 ∈ H := by
        have : (κ p.1)⁻¹ * κ q.1 = (p.2 : G) * (q.2 : G)⁻¹ := by
          calc (κ p.1)⁻¹ * κ q.1 = (κ p.1)⁻¹ * (κ q.1 * (q.2 : G)) * (q.2 : G)⁻¹ := by group
            _ = (κ p.1)⁻¹ * (κ p.1 * (p.2 : G)) * (q.2 : G)⁻¹ := by rw [he]
            _ = (p.2 : G) * (q.2 : G)⁻¹ := by group
        rw [this]
        exact H.mul_mem p.2.2 (H.inv_mem q.2.2)
      have h1 := hinj _ (ball_subset_ball hρr hp.1) _ (ball_subset_ball hρr hq.1) hm
      rw [h1] at he
      have h2 : (p.2 : G) = q.2 := mul_left_cancel he
      exact Prod.ext h1 (Subtype.ext h2)
    exact (measurableSet_ball.prod MeasurableSet.univ).image_of_continuousOn_injOn hc hi
  · intro ρ s hρ hρr hs hsr
    have hB := hbox ρ s hρr hsr
    have hBm : MeasurableSet (ball (0 : EuclideanSpace ℝ ι) ρ ×ˢ ball (0 : EuclideanSpace ℝ η) s) :=
      measurableSet_ball.prod measurableSet_ball
    have hF2 : ∀ p ∈ ball (0 : EuclideanSpace ℝ ι) ρ ×ˢ ball (0 : EuclideanSpace ℝ η) s,
        HasFDerivWithinAt F (F' p) (ball (0 : EuclideanSpace ℝ ι) ρ ×ˢ ball (0 : EuclideanSpace ℝ η) s) p :=
      fun p hp => (hF p (hB hp)).mono hB
    have e2 : (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η => κ p.1 * (χ p.2 : G)) ''
        (ball 0 ρ ×ˢ ball 0 s) = φ '' (F '' (ball 0 ρ ×ˢ ball 0 s)) := by
      rw [image_image]
      exact image_congr fun p hp => hΦ p (hB hp)
    rw [himg, e2, hφ _ ((image_mono hB).trans hFU) (measurable_image_of_fderivWithin hBm hF2 (hFi.mono hB)),
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hBm hF2 (hFi.mono hB)]
    simp_rw [ENNReal.ofReal_mul (abs_nonneg _)]
end PI.AprimeInfG
