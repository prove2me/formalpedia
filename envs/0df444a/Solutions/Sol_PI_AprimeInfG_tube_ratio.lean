-- Prove2me | solution 1 for PI.AprimeInfG.tube_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:06:19.333466+00:00
-- url     : https://prove2.me/submissions/d7817113-de96-48ca-90b7-f08e9cfcd219

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_GrpTube
import Theorems.Thm_PI_AprimeInfG_tube_bounds

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
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant]
    [SFinite ν] (hν0 : ν univ ≠ 0) (hνf : ν univ ≠ ∞) {ι η : Type} [Fintype ι] [Fintype η]
    {κ : EuclideanSpace ℝ ι → G} {χ : EuclideanSpace ℝ η → H} {r0 : ℝ} {d : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ}
    {e : EuclideanSpace ℝ η → ℝ} (hC : TubeChart μ H ν κ χ r0 d e) (hd : ContinuousAt d 0) (hd0 : 0 < d 0)
    (he : ContinuousAt e 0) (he0 : 0 < e 0) :
    (∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ0 → MeasurableSet (tubeS H (κ '' ball 0 ρ) univ) ∧
      0 < μ (tubeS H (κ '' ball 0 ρ) univ) ∧ μ (tubeS H (κ '' ball 0 ρ) univ) < ⊤) ∧
    Tendsto (fun ρ => (μ (tubeS H (κ '' ball 0 ρ) univ)).toReal / (volume (ball (0 : EuclideanSpace ℝ ι) ρ)).toReal)
      (𝓝[>] 0) (𝓝 (d 0 / e 0 * (ν univ).toReal)) := by

  have hrad : ∀ ε > 0, ∃ s, 0 < s ∧ s ≤ r0 ∧
      (∀ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η, ‖p‖ < s → |d p - d 0| < ε) ∧
      (∀ y : EuclideanSpace ℝ η, ‖y‖ < s → |e y - e 0| < ε) := by
    intro ε hε
    obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousAt_iff.1 hd ε hε
    obtain ⟨δ2, hδ2, h2⟩ := Metric.continuousAt_iff.1 he ε hε
    refine ⟨min (min δ1 δ2) r0, lt_min (lt_min hδ1 hδ2) hC.pos, min_le_right _ _, ?_, ?_⟩
    · intro p hp
      have := h1 (x := p) (by rw [dist_zero_right]; exact hp.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
      rwa [Real.dist_eq] at this
    · intro y hy
      have := h2 (x := y) (by rw [dist_zero_right]; exact hy.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
      rwa [Real.dist_eq] at this
  constructor
  · have hε : 0 < min (d 0) (e 0) / 2 := by positivity
    obtain ⟨s, hs, hsr, hdε, heε⟩ := hrad _ hε
    refine ⟨s, hs, fun ρ hρ hρs => ?_⟩
    have hm := min_le_left (d 0) (e 0)
    have hm' := min_le_right (d 0) (e 0)
    obtain ⟨h1, h2, -, -⟩ := tube_bounds μ H ν hν0 hνf hC hε (by linarith) (by linarith) hs hsr hρ hρs.le hdε heε
    exact ⟨hC.mH ρ hρ (hρs.le.trans hsr), h1, h2⟩
  · set T := d 0 / e 0 * (ν univ).toReal with hT
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro δ hδ
    have hU : Tendsto (fun ε : ℝ => (d 0 + ε) / (e 0 - ε) * (ν univ).toReal) (𝓝 0) (𝓝 T) := by
      have : ContinuousAt (fun ε : ℝ => (d 0 + ε) / (e 0 - ε) * (ν univ).toReal) 0 :=
        ((continuousAt_const.add continuousAt_id).div (continuousAt_const.sub continuousAt_id)
          (by simp; exact he0.ne')).mul continuousAt_const
      simpa [hT] using this.tendsto
    have hL : Tendsto (fun ε : ℝ => (d 0 - ε) / (e 0 + ε) * (ν univ).toReal) (𝓝 0) (𝓝 T) := by
      have : ContinuousAt (fun ε : ℝ => (d 0 - ε) / (e 0 + ε) * (ν univ).toReal) 0 :=
        ((continuousAt_const.sub continuousAt_id).div (continuousAt_const.add continuousAt_id)
          (by simp; exact he0.ne')).mul continuousAt_const
      simpa [hT] using this.tendsto
    have ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < d 0 ∧ ε < e 0 ∧
        (d 0 + ε) / (e 0 - ε) * (ν univ).toReal < T + δ ∧ T - δ < (d 0 - ε) / (e 0 + ε) * (ν univ).toReal := by
      refine Filter.Eventually.and (eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0)) (nhdsWithin_le_nhds ?_)
      refine (gt_mem_nhds hd0).and ((gt_mem_nhds he0).and
        ((hU.eventually (gt_mem_nhds (by linarith : T < T + δ))).and
          (hL.eventually (lt_mem_nhds (by linarith : T - δ < T)))))
    obtain ⟨ε, hε, hεd, hεe, hεU, hεL⟩ := ev.exists
    obtain ⟨s, hs, hsr, hdε, heε⟩ := hrad ε hε
    refine ⟨s, hs, fun {ρ} hρ hρd => ?_⟩
    have hρ' : 0 < ρ := hρ
    have hρs : ρ ≤ s := by rw [Real.dist_eq, sub_zero, abs_of_pos hρ'] at hρd; exact hρd.le
    obtain ⟨-, -, hlo, hhi⟩ := tube_bounds μ H ν hν0 hνf hC hε hεd hεe hs hsr hρ' hρs hdε heε
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith
end PI.AprimeInfG
