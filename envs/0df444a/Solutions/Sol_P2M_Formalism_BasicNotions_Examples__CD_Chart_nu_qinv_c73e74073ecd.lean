-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_qinv_c73e74073ecd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:45:24.91557+00:00
-- url     : https://prove2.me/submissions/f60bc8ab-2a82-4154-8063-8406b57a7d98

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LeOfEventuallyDown
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsDensity
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_mat_expG_1363518d9b59
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_apply_3ee47408ca0b
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_distortion_ba7d2bd37f11


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Filter Topology Metric NormedSpace Set
open scoped ENNReal NNReal
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
open Formalism.BasicNotions.Examples₂.CD.Chart
variable {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G] (C : Chart V G)
variable {ρ : ℝ} (hR : ∀ Z : 𝔸, ‖Z‖ < ρ → logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V))
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G)
variable [IsTopologicalGroup G] [μ.IsHaarMeasure]
include hR
namespace Formalism.BasicNotions.Examples₂.CD.Chart
theorem _root_.solution (hρ : 0 < ρ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) : ∃ δ > 0, QInv (C.nu ρ μ) ε δ := by
  obtain ⟨κ, hκ, hd⟩ := distortion (𝔸 := 𝔸) (half_pos hε0)
  refine ⟨min κ ρ / 3, by positivity, ?_⟩
  intro X hX r hr0 hrδ
  have hm1 : min κ ρ ≤ κ := min_le_left _ _
  have hm2 : min κ ρ ≤ ρ := min_le_right _ _
  have hXn : ‖(X : 𝔸)‖ < min κ ρ / 3 := hX
  have hX0 : 0 ≤ ‖(X : 𝔸)‖ := norm_nonneg _
  have hmul : ∀ a b : G, C.mat (a * b) = C.mat a * C.mat b := fun a b => map_mul _ _ _
  constructor
  · rw [C.nu_apply hR μ measurableSet_closedBall, C.nu_apply hR μ measurableSet_closedBall,
      ← measure_smul μ (C.expG (-X))]
    apply measure_mono
    rintro _ ⟨_, ⟨Y, ⟨hY1, hY2⟩, rfl⟩, rfl⟩
    have hW : ‖(Y : 𝔸) - X‖ ≤ (1 - ε) * r := by
      rw [mem_closedBall_iff_norm] at hY1
      exact hY1
    have hW0 : 0 ≤ ‖(Y : 𝔸) - X‖ := norm_nonneg _
    have hWk : ‖(Y : 𝔸) - X‖ < κ := by nlinarith
    obtain ⟨⟨he, hn⟩, -⟩ := hd X ((Y : 𝔸) - X) (by linarith) hWk
    have hXY : (X : 𝔸) + ((Y : 𝔸) - X) = Y := by abel
    rw [hXY] at he
    have h1 := norm_sub_norm_le (F1 ((X : 𝔸), (Y : 𝔸) - X)) ((Y : 𝔸) - X)
    have hp : (1 + ε / 2) * ‖(Y : 𝔸) - X‖ ≤ (1 + ε / 2) * ((1 - ε) * r) :=
      mul_le_mul_of_nonneg_left hW (by linarith)
    have hq : (1 + ε / 2) * ((1 - ε) * r) ≤ r := by
      nlinarith [mul_pos hε0 hr0, mul_pos (mul_pos hε0 hε0) hr0]
    have hZn : ‖F1 ((X : 𝔸), (Y : 𝔸) - X)‖ ≤ r := by linarith
    have hZρ : ‖F1 ((X : 𝔸), (Y : 𝔸) - X)‖ < ρ := by linarith
    have hex : exp (F1 ((X : 𝔸), (Y : 𝔸) - X)) = C.mat (C.expG (-X) * C.expG Y) := by
      rw [hmul, C.mat_expG, C.mat_expG, he, Submodule.coe_neg]
    have hZV := (hR _ hZρ).2 ⟨_, hex.symm⟩
    refine ⟨⟨_, hZV⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_closedBall_zero_iff]
      exact hZn
    · rw [mem_ball_zero_iff]
      exact hZρ
    · apply C.emb.injective
      rw [C.mat_expG]
      exact hex
  · rw [C.nu_apply hR μ measurableSet_closedBall, C.nu_apply hR μ measurableSet_closedBall,
      ← measure_smul μ (C.expG X)]
    apply measure_mono
    rintro _ ⟨_, ⟨Z, ⟨hZ1, hZ2⟩, rfl⟩, rfl⟩
    have hZ : ‖(Z : 𝔸)‖ ≤ r := by
      rw [mem_closedBall_zero_iff] at hZ1
      exact hZ1
    have hZ0 : 0 ≤ ‖(Z : 𝔸)‖ := norm_nonneg _
    obtain ⟨-, ⟨he, hn⟩⟩ := hd X Z (by linarith) (by linarith)
    have h1 := norm_sub_norm_le (F2 ((X : 𝔸), (Z : 𝔸)) - X) (Z : 𝔸)
    have hp : ε / 2 * ‖(Z : 𝔸)‖ ≤ ε / 2 * r := mul_le_mul_of_nonneg_left hZ (by linarith)
    have hq : ε * r ≤ r := by nlinarith [mul_pos hε0 hr0]
    have hYX : ‖F2 ((X : 𝔸), (Z : 𝔸)) - X‖ ≤ (1 + ε) * r := by
      calc ‖F2 ((X : 𝔸), (Z : 𝔸)) - X‖ ≤ ‖F2 ((X : 𝔸), (Z : 𝔸)) - X - Z‖ + ‖(Z : 𝔸)‖ := by linarith [h1]
        _ ≤ ε / 2 * ‖(Z : 𝔸)‖ + r := add_le_add hn hZ
        _ ≤ ε / 2 * r + r := by linarith [hp]
        _ ≤ (1 + ε) * r := by nlinarith [mul_pos hε0 hr0]
    have h2 := norm_le_insert' (F2 ((X : 𝔸), (Z : 𝔸))) (X : 𝔸)
    have hYρ : ‖F2 ((X : 𝔸), (Z : 𝔸))‖ < ρ := by linarith
    have hex : exp (F2 ((X : 𝔸), (Z : 𝔸))) = C.mat (C.expG X * C.expG Z) := by
      rw [hmul, C.mat_expG, C.mat_expG, he]
    have hYV := (hR _ hYρ).2 ⟨_, hex.symm⟩
    refine ⟨⟨_, hYV⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_closedBall_iff_norm]
      exact hYX
    · rw [mem_ball_zero_iff]
      exact hYρ
    · apply C.emb.injective
      rw [C.mat_expG]
      exact hex
end Formalism.BasicNotions.Examples₂.CD.Chart
