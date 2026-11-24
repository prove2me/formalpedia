-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IsParam.translate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:53.48987+00:00
-- url     : https://prove2.me/submissions/94371c7e-c1ef-4d75-b9aa-4815d4d4b9e8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gaap_mem_ball_add
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
namespace IsParam
theorem _root_.solution {P : Ideal (MvPolynomial (Ix κ) ℤ)} {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → Ix κ → ℂ} (h : IsParam P U γ) (y₀ : Fin D → ℂ) {ρ₀ : ℝ}
    (hball : Metric.ball y₀ ρ₀ ⊆ U) :
    IsParam P (Metric.ball 0 ρ₀) fun y => γ (y₀ + y) := by
  obtain ⟨_, hd, hpts, O, q, hO, hq, hOeq, hsc, hqγ⟩ := h
  have hmaps : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, y₀ + y ∈ U := fun y hy =>
    hball (gaap_mem_ball_add.2 hy)
  have hγO : ∀ y ∈ U, γ y ∈ O := fun y hy => by
    have : γ y ∈ coneOver U γ := ⟨y, hy, 1, one_ne_zero, (one_smul ℂ _).symm⟩
    rw [← hOeq] at this
    exact this.1
  refine ⟨Metric.isOpen_ball, ?_, fun y hy => hpts _ (hmaps y hy),
    O ∩ q ⁻¹' Metric.ball y₀ ρ₀, fun z => q z - y₀,
    hq.continuousOn.isOpen_inter_preimage hO Metric.isOpen_ball,
    (hq.mono Set.inter_subset_left).sub analyticOnNhd_const, ?_, ?_, ?_⟩
  · exact hd.comp (analyticOnNhd_const.add analyticOnNhd_id) fun y hy => hmaps y hy
  · ext z
    constructor
    · rintro ⟨⟨hzO, hzq⟩, hzp⟩
      have hz : z ∈ coneOver U γ := hOeq ▸ ⟨hzO, hzp⟩
      obtain ⟨y, hyU, c, hc, rfl⟩ := hz
      have h1 : q (c • γ y) = y := by rw [(hsc _ (hγO y hyU) c hc).2, hqγ y hyU]
      have hy : y ∈ Metric.ball y₀ ρ₀ := by
        have := hzq
        simp only [Set.mem_preimage, h1] at this
        exact this
      refine ⟨y - y₀, ?_, c, hc, ?_⟩
      · rw [← gaap_mem_ball_add (y₀ := y₀), add_sub_cancel]
        exact hy
      · simp
    · rintro ⟨y, hy, c, hc, rfl⟩
      have hcone : c • γ (y₀ + y) ∈ coneOver U γ := ⟨y₀ + y, hmaps y hy, c, hc, rfl⟩
      rw [← hOeq] at hcone
      refine ⟨⟨hcone.1, ?_⟩, hcone.2⟩
      simp only [Set.mem_preimage]
      rw [(hsc _ (hγO _ (hmaps y hy)) c hc).2, hqγ _ (hmaps y hy)]
      exact gaap_mem_ball_add.2 hy
  · rintro z ⟨hzO, hzq⟩ c hc
    have := hsc z hzO c hc
    refine ⟨⟨this.1, ?_⟩, ?_⟩
    · simp only [Set.mem_preimage, this.2]
      exact hzq
    · simp only [this.2]
  · intro y hy
    simp only
    rw [hqγ _ (hmaps y hy), add_sub_cancel_left]
end IsParam
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
