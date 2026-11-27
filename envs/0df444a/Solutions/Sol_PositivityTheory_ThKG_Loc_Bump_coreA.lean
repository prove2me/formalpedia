-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.coreA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:22:45.266158+00:00
-- url     : https://prove2.me/submissions/94844cf3-7230-455e-807f-31dbc977f9ba

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ContinuousOnRationalWeight
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_norm_rationalWeight_le
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_integrable_mj
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_Dec_bound
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_continuousOn_rationalWeight
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_open_U
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_continuous_ch
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_core_bump
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_fourier_vanish
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_measurable_reduced_size
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_norm_ch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf



set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped SchwartzMap RealInnerProductSpace
variable {ι : Type} [Fintype ι] {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X] {K : Type} [TopologicalSpace K] [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution (μ : Measure K) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] {π : K × (ι → ℂ) → X} {x₀ : X} (hπ : Prp π x₀)
    (κ : ι → ℕ) (e : ℕ) {a : K × (ι → ℂ) → ℂ} (ha : Continuous a) (hd : Dec a) (c : ℂ)
    (hpos : ∀ p, π p = x₀ → 0 < (a p * r0 κ e p.2 * c).re)
    (h : ∀ η, ∫ k, ∫ x, ch ⟪η, π (k, x)⟫ * a (k, x) * r0 κ e x ∂volume ∂μ = 0) : False := by
  obtain ⟨ε, S, hε, hS, hSU, hb⟩ := hπ.cpt
  obtain ⟨p₀, h₀⟩ := hπ.pt
  obtain ⟨φ, -, -, hφ⟩ := core_bump (μ.prod volume) π hπ.cont x₀ (fun p => a p * r0 κ e p.2 * c) _ S open_U
    ((ha.continuousOn.mul ((continuousOn_rationalWeight κ e).comp continuous_snd.continuousOn fun p hp => hp)).mul continuousOn_const)
    hS hSU ε hε hb hpos p₀ h₀
  obtain ⟨C, N, -, hC⟩ := hd.bound (2 * e * Fintype.card ι)
  have hi : Integrable (fun p : K × (ι → ℂ) => a p * r0 κ e p.2) (μ.prod volume) := by
    refine ((integrable_const C).mul_prod integrable_mj).mono'
      (ha.measurable.mul ((measurable_reduced_size κ e).comp measurable_snd)).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    have := hC p.1 p.2 0
    simp only [add_zero, norm_zero, one_pow, mul_one] at this
    rw [norm_mul]
    exact le_trans (by gcongr; exact norm_rationalWeight_le κ e p.2) this
  refine hφ (fourier_vanish _ π hπ.cont.measurable _ (hi.mul_const c) (fun η => ?_) φ)
  simp only [← mul_assoc]
  rw [integral_mul_const, integral_prod, h, zero_mul]
  simp only [mul_assoc]
  exact hi.bdd_mul (c := 1) (continuous_ch.comp (continuous_const.inner hπ.cont)).aestronglyMeasurable
    (Eventually.of_forall fun q => (norm_ch _).le)
end PositivityTheory.ThKG.Loc.Bump
