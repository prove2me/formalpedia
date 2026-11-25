-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_punctured_factor_5fc13254861c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:36:06.210713+00:00
-- url     : https://prove2.me/submissions/3ba4e19f-6b90-42cb-8829-afc3de4a28f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedBranchSameOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedCurveDiscInverse
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPuncturedBranchSameOrder
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_disc_props_e21f27b8168e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_factor_of_punctured_43801c6296a6

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
noncomputable section
open GroundTheory.Heights₂.Heights.PuncturedBranchSameOrder
namespace GroundTheory.Heights₂.Heights.PuncturedBranchSameOrder
theorem _root_.solution (hcut : PuncturedCurveDiscInverse.Statement) {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}
    {q : Fin n → ℂ} (hI : IsRadicalAt I q) (hdim : ringKrullDim (curveLocalRing I q) = 1) (c d : VarBranch I 1 q)
    (ρ : ℝ) (hρ : 0 < ρ) (hcd : ∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < ρ → d.toFun (fun _ ↦ τ) ∈ c.image) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ (∀ᶠ τ in 𝓝 0, (d.toFun fun _ ↦ τ) = c.toFun fun _ ↦ g τ) ∧
      𝓝 0 ≤ map g (𝓝 0) := by
  obtain ⟨hCd, hCi, hCm, hC0, hCim⟩ := disc_props c
  obtain ⟨hDd, hDi, hDm, hD0, -⟩ := disc_props d
  obtain ⟨ε, hε, hcutε⟩ := hcut n I q hI hdim
  have hDc : ContinuousAt (fun τ : ℂ ↦ d.toFun fun _ ↦ τ) 0 :=
    (hDd.differentiableAt (Metric.ball_mem_nhds 0 d.radius_pos)).continuousAt
  obtain ⟨ρ₁, hρ₁, hρ₁ε⟩ := Metric.continuousAt_iff.1 hDc ε hε
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : ℝ, ρ' = min (min ρ ρ₁) d.radius := ⟨_, rfl⟩
  have hρ'pos : 0 < ρ' := hρ' ▸ lt_min (lt_min hρ hρ₁) d.radius_pos
  have hρ'ρ : ρ' ≤ ρ := hρ' ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hρ'1 : ρ' ≤ ρ₁ := hρ' ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hsub : Metric.ball (0 : ℂ) ρ' ⊆ Metric.ball 0 d.radius := Metric.ball_subset_ball (hρ' ▸ min_le_right _ _)
  let ψ : ℂ → ℂ := fun τ ↦
    Function.invFunOn (fun σ : ℂ ↦ c.toFun fun _ ↦ σ) (Metric.ball 0 c.radius) (d.toFun fun _ ↦ τ)
  have hψ : ∀ τ ∈ Metric.ball (0 : ℂ) ρ' \ {0},
      ψ τ ∈ Metric.ball (0 : ℂ) c.radius ∧ (c.toFun fun _ ↦ ψ τ) = d.toFun fun _ ↦ τ := by
    intro τ hτ
    have hex := (hCim _).1 (hcd τ (norm_pos_iff.2 hτ.2) (lt_of_lt_of_le (mem_ball_zero_iff.1 hτ.1) hρ'ρ))
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
  have hopen : IsOpen (Metric.ball (0 : ℂ) ρ' \ {0}) := Metric.isOpen_ball.sdiff isClosed_singleton
  have hψd : DifferentiableOn ℂ ψ (Metric.ball 0 ρ' \ {0}) := by
    intro τ₀ hτ₀
    obtain ⟨hσ₀r, hσ₀⟩ := hψ τ₀ hτ₀
    have hδ : 0 < c.radius - ‖ψ τ₀‖ := sub_pos.2 (mem_ball_zero_iff.1 hσ₀r)
    have hballsub : Metric.ball (ψ τ₀) (c.radius - ‖ψ τ₀‖) ⊆ Metric.ball 0 c.radius :=
      Metric.ball_subset_ball' (by rw [dist_zero_right]; linarith)
    have hne : (d.toFun fun _ ↦ τ₀) ≠ q := fun h ↦
      hτ₀.2 (hDi (hsub hτ₀.1) (Metric.mem_ball_self d.radius_pos) (h.trans hD0.symm))
    have hε₀ : (d.toFun fun _ ↦ τ₀) ∈ Metric.ball q ε := by
      have := hρ₁ε (x := τ₀) (by rw [dist_zero_right]; exact lt_of_lt_of_le (mem_ball_zero_iff.1 hτ₀.1) hρ'1)
      rw [Metric.mem_ball]
      rwa [hD0] at this
    obtain ⟨U, hUo, hUx, Ψ, hΨd, hΨ⟩ := hcutε (fun σ ↦ c.toFun fun _ ↦ σ) (ψ τ₀) (c.radius - ‖ψ τ₀‖) hδ
      (hCd.mono hballsub) (hCi.mono hballsub) (fun σ hσ ↦ hCm (hballsub hσ))
      (by show (c.toFun fun _ ↦ ψ τ₀) ∈ Metric.ball q ε; rw [hσ₀]; exact hε₀)
      (by show (c.toFun fun _ ↦ ψ τ₀) ≠ q; rw [hσ₀]; exact hne)
    have hUD : (d.toFun fun _ ↦ τ₀) ∈ U := by
      have hUx' : (c.toFun fun _ ↦ ψ τ₀) ∈ U := hUx
      rwa [hσ₀] at hUx'
    have hDdiff : DifferentiableAt ℂ (fun τ : ℂ ↦ d.toFun fun _ ↦ τ) τ₀ :=
      hDd.differentiableAt (Metric.isOpen_ball.mem_nhds (hsub hτ₀.1))
    have hevU : ∀ᶠ τ in 𝓝 τ₀, (d.toFun fun _ ↦ τ) ∈ U :=
      hDdiff.continuousAt.preimage_mem_nhds (hUo.mem_nhds hUD)
    have heq : ψ =ᶠ[𝓝 τ₀] fun τ ↦ Ψ (d.toFun fun _ ↦ τ) := by
      filter_upwards [hevU, hopen.mem_nhds hτ₀] with τ hτU hτ
      obtain ⟨σ, hσ, hσz, hΨσ⟩ := hΨ (d.toFun fun _ ↦ τ) ⟨hDm (hsub hτ.1), hτU⟩
      rw [hΨσ]
      exact hCi (hψ τ hτ).1 (hballsub hσ) ((hψ τ hτ).2.trans hσz.symm)
    have hdiff : DifferentiableAt ℂ (fun τ ↦ Ψ (d.toFun fun _ ↦ τ)) τ₀ :=
      (hΨd.differentiableAt (hUo.mem_nhds hUD)).comp τ₀ hDdiff
    exact (hdiff.congr_of_eventuallyEq heq).differentiableWithinAt
  exact factor_of_punctured (C := fun σ : ℂ ↦ c.toFun fun _ ↦ σ) (D := fun τ : ℂ ↦ d.toFun fun _ ↦ τ)
    c.radius_pos hρ'pos hCd hCi (hDd.mono hsub) (hDi.mono hsub) (hC0.trans hD0.symm) hψd hψ
end GroundTheory.Heights₂.Heights.PuncturedBranchSameOrder
