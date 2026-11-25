-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hadamard_decomposition_4d7972bd588d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:31:42.541631+00:00
-- url     : https://prove2.me/submissions/cc4437e3-2745-480a-b1e6-b619b59868d2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermPointIdealSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolGermPointIdealSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] {w : σ → ℂ} {f : (σ → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f w) :
    ∃ g : σ → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (g i) w) ∧
      ∀ᶠ z in 𝓝 w, f z = f w + ∑ i, (z i - w i) * g i z := by
  classical
  obtain ⟨p, r, hp⟩ := hf
  have hrad : p.shift.radius = p.radius := FormalMultilinearSeries.radius_shift p
  have hq : 0 < p.shift.radius := by rw [hrad]; exact lt_of_lt_of_le hp.r_pos hp.r_le
  have hG : HasFPowerSeriesOnBall p.shift.sum p.shift 0 p.shift.radius :=
    p.shift.hasFPowerSeriesOnBall hq
  refine ⟨fun i z => p.shift.sum (z - w) (Pi.single i 1), fun i => ?_, ?_⟩
  · have h2 : AnalyticAt ℂ (fun z : σ → ℂ => z - w) w := analyticAt_id.sub analyticAt_const
    have h3 : AnalyticAt ℂ p.shift.sum ((fun z : σ → ℂ => z - w) w) := by
      simpa using hG.analyticAt
    exact ((ContinuousLinearMap.apply ℂ ℂ (Pi.single i (1 : ℂ))).analyticAt _).comp
      (AnalyticAt.comp (g := p.shift.sum) (f := fun z : σ → ℂ => z - w) h3 h2)
  · filter_upwards [Metric.eball_mem_nhds w hp.r_pos] with z hz
    set y := z - w with hy
    have hy0 : y ∈ Metric.eball (0 : σ → ℂ) r := by
      rw [Metric.mem_eball] at hz ⊢
      rwa [edist_zero_right, hy, ← edist_eq_enorm_sub]
    have hy1 : y ∈ Metric.eball (0 : σ → ℂ) p.shift.radius :=
      Metric.eball_subset_eball (hrad ▸ hp.r_le) hy0
    have h1 := hp.hasSum hy0
    have h2 := hG.hasSum hy1
    rw [zero_add] at h2
    have h3 := (ContinuousLinearMap.apply ℂ ℂ y).hasSum h2
    have h4 : ∀ n, (ContinuousLinearMap.apply ℂ ℂ y) (p.shift n fun _ => y) =
        p (n + 1) fun _ => y := by
      intro n
      simp only [ContinuousLinearMap.apply_apply, FormalMultilinearSeries.shift,
        ContinuousMultilinearMap.curryRight_apply]
      congr 1
      funext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;> simp
    simp only [h4, ContinuousLinearMap.apply_apply] at h3
    have h5 := (hasSum_nat_add_iff' 1).mpr h1
    simp only [Finset.range_one, Finset.sum_singleton, hp.coeff_zero] at h5
    have e := h5.unique h3
    have hwz : w + y = z := by rw [hy]; abel
    rw [hwz] at e
    have e2 : p.shift.sum y y = ∑ i, (z i - w i) * p.shift.sum y (Pi.single i 1) := by
      have hyy : p.shift.sum y y = p.shift.sum y (∑ i, Pi.single i (y i)) := by
        rw [Finset.univ_sum_single]
      rw [hyy, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (Pi.single i (y i) : σ → ℂ) = y i • Pi.single i 1 by
        ext j; by_cases h : j = i
        · subst h; simp
        · simp [h], map_smul, smul_eq_mul, hy, Pi.sub_apply]
    rw [← e2, ← e]
    ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
