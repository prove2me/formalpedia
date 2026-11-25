-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.Chart.nu_qinv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:41:42.917881+00:00
-- url     : https://prove2.me/submissions/84a4e30f-8dfc-492b-84af-399d028b4456

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_exp_mul_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_distortion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_mat_expG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_nu_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HExp
open MeasureTheory Filter Topology Metric NormedSpace Set
open scoped ENNReal NNReal
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
open ReciprocityTheory.ChartRestriction.DS.HExp.Chart
variable {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G] (C : Chart V G)
variable {ρ : ℝ} (hR : ∀ Z : 𝔸, ‖Z‖ < ρ → logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V))
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G)
variable [IsTopologicalGroup G] [μ.IsHaarMeasure]
include hR
namespace ReciprocityTheory.ChartRestriction.DS.HExp.Chart
theorem _root_.solution (hρ : 0 < ρ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) : ∃ δ > 0, QInv (C.nu ρ μ) ε δ := by
  obtain ⟨δ0, hδ0, hD⟩ := distortion (𝔸 := 𝔸) hε0
  refine ⟨min δ0 (ρ / 4), by positivity, fun X hX r hr0 hr => ?_⟩
  have hXδ : ‖(X : 𝔸)‖ < δ0 := lt_of_lt_of_le hX (min_le_left _ _)
  have hXρ : ‖(X : 𝔸)‖ < ρ / 4 := lt_of_lt_of_le hX (min_le_right _ _)
  have hrδ : r < δ0 := lt_of_lt_of_le hr (min_le_left _ _)
  have hrρ : r < ρ / 4 := lt_of_lt_of_le hr (min_le_right _ _)
  rw [C.nu_apply hR μ measurableSet_closedBall, C.nu_apply hR μ measurableSet_closedBall,
    C.nu_apply hR μ measurableSet_closedBall]
  constructor
  · rw [← measure_preimage_mul μ (C.expG X)⁻¹ (C.expG '' (closedBall 0 r ∩ ball 0 ρ))]
    refine measure_mono ?_
    rintro _ ⟨W, ⟨hW, -⟩, rfl⟩
    set Y : V := W - X with hY
    have hYn : ‖(Y : 𝔸)‖ ≤ (1 - ε) * r := by
      have := mem_closedBall_iff_norm.mp hW
      exact this
    have hYr : ‖(Y : 𝔸)‖ < δ0 := by nlinarith
    obtain ⟨⟨e1, e2⟩, -⟩ := hD X Y hXδ hYr
    have hZn : ‖F1 ((X : 𝔸), (Y : 𝔸))‖ ≤ r := by
      have h1 : ‖F1 ((X : 𝔸), (Y : 𝔸))‖ ≤ ‖F1 ((X : 𝔸), (Y : 𝔸)) - Y‖ + ‖(Y : 𝔸)‖ := by
        have := norm_add_le (F1 ((X : 𝔸), (Y : 𝔸)) - Y) (Y : 𝔸)
        simpa using this
      have h2 : (1 + ε) * ((1 - ε) * r) ≤ r := by nlinarith [mul_pos hε0 hε0]
      nlinarith [norm_nonneg (Y : 𝔸)]
    have hXY : (X : 𝔸) + (Y : 𝔸) = (W : 𝔸) := by simp [hY]
    have hZV : F1 ((X : 𝔸), (Y : 𝔸)) ∈ V := by
      refine (hR _ (by linarith)).2 ⟨C.expG (-X) * C.expG W, ?_⟩
      rw [map_mul, mat_expG, mat_expG, e1, hXY]
      simp
    refine ⟨⟨_, hZV⟩, ⟨?_, ?_⟩, C.emb.injective ?_⟩
    · rw [mem_closedBall_zero_iff]; exact hZn
    · rw [mem_ball_zero_iff]
      have : ‖F1 ((X : 𝔸), (Y : 𝔸))‖ < ρ := by linarith
      exact this
    · have hinv : C.mat (C.expG X)⁻¹ = exp (-(X : 𝔸)) := by
        have h1 : C.mat (C.expG X)⁻¹ * C.mat (C.expG X) = 1 := by rw [← map_mul]; simp
        rw [mat_expG] at h1
        calc C.mat (C.expG X)⁻¹ = C.mat (C.expG X)⁻¹ * (exp (X : 𝔸) * exp (-(X : 𝔸))) := by
              rw [exp_mul_neg, mul_one]
          _ = exp (-(X : 𝔸)) := by rw [← mul_assoc, h1, one_mul]
      rw [mat_expG, map_mul, hinv, mat_expG]
      show exp (F1 ((X : 𝔸), (Y : 𝔸))) = _
      rw [e1, hXY]
  · rw [← measure_preimage_mul μ (C.expG X) (C.expG '' (closedBall X ((1 + ε) * r) ∩ ball 0 ρ))]
    refine measure_mono ?_
    rintro _ ⟨Z, ⟨hZ, -⟩, rfl⟩
    have hZn : ‖(Z : 𝔸)‖ ≤ r := by
      have := mem_closedBall_zero_iff.mp hZ
      exact this
    obtain ⟨-, ⟨e1, e2⟩⟩ := hD X Z hXδ (lt_of_le_of_lt hZn hrδ)
    have h1 : ‖F2 ((X : 𝔸), (Z : 𝔸)) - X‖ ≤ (1 + ε) * r := by
      have := norm_add_le (F2 ((X : 𝔸), (Z : 𝔸)) - X - Z) (Z : 𝔸)
      have e : F2 ((X : 𝔸), (Z : 𝔸)) - X - Z + Z = F2 ((X : 𝔸), (Z : 𝔸)) - X := by abel
      rw [e] at this
      nlinarith [norm_nonneg (Z : 𝔸)]
    have h2 : ‖F2 ((X : 𝔸), (Z : 𝔸))‖ < ρ := by
      have := norm_add_le (F2 ((X : 𝔸), (Z : 𝔸)) - X) (X : 𝔸)
      have e : F2 ((X : 𝔸), (Z : 𝔸)) - X + X = F2 ((X : 𝔸), (Z : 𝔸)) := by abel
      rw [e] at this
      nlinarith
    have hV : F2 ((X : 𝔸), (Z : 𝔸)) ∈ V := by
      refine (hR _ h2).2 ⟨C.expG X * C.expG Z, ?_⟩
      rw [map_mul, mat_expG, mat_expG, e1]
    refine ⟨⟨_, hV⟩, ⟨?_, ?_⟩, C.emb.injective ?_⟩
    · rw [mem_closedBall_iff_norm]; exact h1
    · rw [mem_ball_zero_iff]; exact h2
    · rw [mat_expG, map_mul, mat_expG, mat_expG]
      exact e1
end ReciprocityTheory.ChartRestriction.DS.HExp.Chart
