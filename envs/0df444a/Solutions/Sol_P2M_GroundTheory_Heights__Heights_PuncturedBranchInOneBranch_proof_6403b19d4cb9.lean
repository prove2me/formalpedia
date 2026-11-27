-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PuncturedBranchInOneBranch_proof_6403b19d4cb9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:08:39.131409+00:00
-- url     : https://prove2.me/submissions/e06f72d4-e620-41eb-b41d-1ff22ed1d331

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedBranchInOneBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchImageNhdOffCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPuncturedBranchInOneBranch
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isPreconnected_punctured_ball_7486948dcaa3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets Filter Topology
namespace GroundTheory.Heights₂.Heights
namespace PuncturedBranchInOneBranch
theorem _root_.solution (h₁ : BranchImageNhdOffCentre.Statement) :
    PuncturedBranchInOneBranch.Statement := by
  intro n I q m c ν ρ _ hdim hρ hcov hdisj
  obtain ⟨N, hN, hNc⟩ := h₁ n I q hdim
  have hnorm : ∀ τ : ℂ, ‖(fun _ ↦ τ : Fin 1 → ℂ)‖ = ‖τ‖ := fun τ ↦ by simp [pi_norm_const]
  have hball : ∀ τ : ℂ, ‖τ‖ < ν.radius → (fun _ ↦ τ : Fin 1 → ℂ) ∈ Metric.ball 0 ν.radius := fun τ hτ ↦ by
    rwa [Metric.mem_ball, dist_zero_right, hnorm]
  have h0r : ‖(0 : ℂ)‖ < ν.radius := by simpa using ν.radius_pos

  have hcont : ∀ τ : ℂ, ‖τ‖ < ν.radius → ContinuousAt (fun τ : ℂ ↦ ν.toFun (fun _ ↦ τ)) τ := fun τ hτ ↦
    (ν.differentiableOn.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds (hball τ hτ))).comp
      (f := fun τ : ℂ ↦ (fun _ ↦ τ : Fin 1 → ℂ)) (continuous_pi fun _ ↦ continuous_id).continuousAt
  have hq : ν.toFun (fun _ ↦ (0 : ℂ)) = q := ν.map_zero
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), ν.toFun (fun _ ↦ τ) ∈ N :=
    (hcont 0 h0r).preimage_mem_nhds (by show N ∈ 𝓝 (ν.toFun fun _ ↦ (0 : ℂ)); rw [hq]; exact hN)
  obtain ⟨ε, hε, hεN⟩ := Metric.eventually_nhds_iff.1 hev

  obtain ⟨R, hR0, hRρ, hRε, hRν⟩ : ∃ R, 0 < R ∧ R ≤ ρ ∧ R ≤ ε ∧ R ≤ ν.radius :=
    ⟨min ρ (min ε ν.radius), lt_min hρ (lt_min hε ν.radius_pos), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  let D : Set ℂ := Metric.ball 0 R \ {0}
  have hD : ∀ τ ∈ D, 0 < ‖τ‖ ∧ ‖τ‖ < R := fun τ hτ ↦
    ⟨norm_pos_iff.2 (by simpa using hτ.2), by simpa using hτ.1⟩
  have hne : ∀ τ ∈ D, ν.toFun (fun _ ↦ τ) ≠ q := by
    intro τ hτ h
    have h' := ν.injOn (hball τ ((hD τ hτ).2.trans_le hRν)) (hball 0 h0r) (h.trans hq.symm)
    exact (norm_pos_iff.1 (hD τ hτ).1) (by simpa using congrFun h' 0)

  let Vb : Fin m → Set ℂ := fun b ↦ D ∩ (fun τ : ℂ ↦ ν.toFun (fun _ ↦ τ)) ⁻¹' (c b).image
  have hDo : IsOpen D := Metric.isOpen_ball.sdiff isClosed_singleton
  have hVo : ∀ b, IsOpen (Vb b) := by
    intro b
    rw [isOpen_iff_mem_nhds]
    rintro τ ⟨hτD, hτb⟩
    have hτN : ν.toFun (fun _ ↦ τ) ∈ N := hεN (by rw [dist_zero_right]; exact (hD τ hτD).2.trans_le hRε)
    obtain ⟨U, hU, hUc⟩ := hNc (c b) _ ⟨hτb, hτN⟩ (hne τ hτD)
    filter_upwards [hDo.mem_nhds hτD, (hcont τ ((hD τ hτD).2.trans_le hRν)).preimage_mem_nhds hU]
      with σ hσD hσU
    exact ⟨hσD, hUc ⟨ν.mapsTo (hball σ ((hD σ hσD).2.trans_le hRν)), hσU⟩⟩
  have hVd : ∀ b b', b ≠ b' → Disjoint (Vb b) (Vb b') := fun b b' hbb ↦
    Set.disjoint_left.2 fun τ hτ hτ' ↦ hne τ hτ.1 (hdisj b b' hbb ⟨hτ.2, hτ'.2⟩)
  have hcovD : ∀ τ ∈ D, ∃ b, τ ∈ Vb b := fun τ hτ ↦ by
    obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (hcov τ (hD τ hτ).1 ((hD τ hτ).2.trans_le hRρ))
    exact ⟨b, hτ, hb⟩

  have hτ₀ : ((R / 2 : ℝ) : ℂ) ∈ D := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    · simp [hR0.ne']
  obtain ⟨b, hb⟩ := hcovD _ hτ₀
  have hsub : D ⊆ Vb b := by
    refine (isPreconnected_punctured_ball hR0).subset_left_of_subset_union (hVo b)
      (isOpen_iUnion fun b' ↦ isOpen_iUnion fun (_ : b' ≠ b) ↦ hVo b') ?_ ?_ ⟨_, hτ₀, hb⟩
    · exact Set.disjoint_iUnion_right.2 fun b' ↦ Set.disjoint_iUnion_right.2 fun hb' ↦ hVd b b' (Ne.symm hb')
    · intro τ hτ
      obtain ⟨b', hb'⟩ := hcovD τ hτ
      by_cases h : b' = b
      · exact Or.inl (h ▸ hb')
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨b', h, hb'⟩)
  refine ⟨b, R, hR0, fun τ hτ0 hτR ↦ (hsub ⟨?_, ?_⟩).2⟩
  · rwa [Metric.mem_ball, dist_zero_right]
  · simpa using norm_pos_iff.1 hτ0
end PuncturedBranchInOneBranch
end GroundTheory.Heights₂.Heights
