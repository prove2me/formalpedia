-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.core_bump
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:00.994201+00:00
-- url     : https://prove2.me/submissions/c7c625a7-5222-46a8-8448-8bfd1da6e5d1

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped FourierTransform SchwartzMap RealInnerProductSpace
variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution {Ω : Type} [TopologicalSpace Ω] [T2Space Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] (π : Ω → X) (hπ : Continuous π) (x₀ : X) (G : Ω → ℂ) (U S : Set Ω)
    (hU : IsOpen U) (hG : ContinuousOn G U) (hS : IsCompact S) (hSU : S ⊆ U) (ε : ℝ) (hε : 0 < ε)
    (hb : ∀ p, dist (π p) x₀ ≤ ε → p ∈ S) (hpos : ∀ p, π p = x₀ → 0 < (G p).re) (p₀ : Ω) (h₀ : π p₀ = x₀) :
    ∃ φ : 𝓢(X, ℂ), (∀ p, φ (π p) ≠ 0 → p ∈ S) ∧ Integrable (fun p => φ (π p) * G p) μ ∧ ∫ p, φ (π p) * G p ∂μ ≠ 0 := by
  have hre : ContinuousOn (fun p => (G p).re) S := Complex.continuous_re.comp_continuousOn (hG.mono hSU)
  have hB : IsCompact (S ∩ (fun p => (G p).re) ⁻¹' Iic 0) :=
    hS.of_isClosed_subset (hre.preimage_isClosed_of_isClosed hS.isClosed isClosed_Iic) inter_subset_left
  have hc : IsClosed (π '' (S ∩ (fun p => (G p).re) ⁻¹' Iic 0)) := (hB.image hπ).isClosed
  have hx : x₀ ∉ π '' (S ∩ (fun p => (G p).re) ⁻¹' Iic 0) := by
    rintro ⟨p, ⟨_, hp⟩, e⟩
    exact absurd (hpos p e) (not_lt.2 hp)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hc.isOpen_compl x₀ hx
  let b : ContDiffBump x₀ := ⟨min δ ε / 2, min δ ε, by positivity, by have := lt_min hδ hε; linarith⟩
  have hbs : ∀ x, b x ≠ 0 → dist x x₀ < min δ ε := fun x h => by
    have : x ∈ Function.support b := h
    rw [b.support_eq] at this
    exact this
  have hcs : HasCompactSupport fun x => ((b x : ℝ) : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hsm : ContDiff ℝ (⊤ : ℕ∞) fun x => ((b x : ℝ) : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hin : ∀ p, b (π p) ≠ 0 → p ∈ S := fun p h => hb p ((hbs _ h).le.trans (min_le_right _ _))
  have hsupp : ∀ {E : Type} [Zero E] [TopologicalSpace E] (g : Ω → E), (∀ p, b (π p) = 0 → g p = 0) → tsupport g ⊆ S := by
    intro E _ _ g hg
    refine closure_minimal (fun p hp => hin p fun h => hp (hg p h)) hS.isClosed
  have hcont : Continuous fun p => ((b (π p) : ℝ) : ℂ) * G p := by
    refine ContinuousOn.continuous_of_tsupport_subset (s := U) ?_ hU ((hsupp _ fun p h => by simp [h]).trans hSU)
    exact ((Complex.continuous_ofReal.comp (b.continuous.comp hπ)).continuousOn).mul hG
  have hk : HasCompactSupport fun p => ((b (π p) : ℝ) : ℂ) * G p :=
    hS.of_isClosed_subset (isClosed_tsupport _) (hsupp _ fun p h => by simp [h])
  have hint := hcont.integrable_of_hasCompactSupport (μ := μ) hk
  refine ⟨hcs.toSchwartzMap hsm, fun p h => hin p fun h' => h (by simp [h']), by simpa using hint, fun h => ?_⟩
  have h1 : ∫ p, (((b (π p) : ℝ) : ℂ) * G p).re ∂μ = 0 := by
    have := integral_re hint
    simp only [RCLike.re_to_complex] at this
    rw [this]
    have h' : ∫ p, ((b (π p) : ℝ) : ℂ) * G p ∂μ = 0 := by simpa using h
    rw [h']; rfl
  have h2 : 0 < ∫ p, (((b (π p) : ℝ) : ℂ) * G p).re ∂μ := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := p₀) (Complex.continuous_re.comp hcont)
      (hk.comp_left (g := Complex.re) rfl) (fun p => ?_) ?_
    · by_cases hp : b (π p) = 0
      · simp [hp]
      · have hS' := hin p hp
        have : 0 < (G p).re := by
          by_contra hn
          exact hball ((hbs _ hp).trans_le (min_le_left _ _)) ⟨p, ⟨hS', not_lt.1 hn⟩, rfl⟩
        simp only [Complex.re_ofReal_mul, Pi.zero_apply]
        exact mul_nonneg b.nonneg this.le
    · have : b (π p₀) = 1 := b.one_of_mem_closedBall (by rw [h₀]; exact Metric.mem_closedBall_self b.rIn_pos.le)
      simp only [Complex.re_ofReal_mul, this, one_mul]
      exact (hpos p₀ h₀).ne'
  exact h2.ne' h1
end PositivityTheory.ThKG.Loc.Bump
