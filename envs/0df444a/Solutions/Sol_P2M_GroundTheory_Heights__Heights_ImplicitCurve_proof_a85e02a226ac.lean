-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ImplicitCurve_proof_a85e02a226ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:56:11.451348+00:00
-- url     : https://prove2.me/submissions/0ffa5352-083e-4843-bf80-63e4e8c00f37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StImplicitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PImplicitCurve
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ImplicitCurve_analyticOnNhd_of_differentiableOn_12cdb7d22a35

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
open Matrix Topology Metric
noncomputable section
open GroundTheory.Heights₂.Heights.ImplicitCurve
namespace GroundTheory.Heights₂.Heights.ImplicitCurve
theorem _root_.solution : ImplicitCurve.Statement := by
  intro n k γ R L s hγ hs hbij
  set F : (Fin (k + 1) → ℂ) → Fin (k + 1) → ℂ := fun t => vecCons (t 0) (L *ᵥ γ t) with hF
  have hFd : DifferentiableOn ℂ F (ball 0 R) := by
    refine differentiableOn_pi.2 fun i => Fin.cases ?_ (fun j => ?_) i
    · simpa [hF] using (differentiableOn_pi.1 (differentiableOn_id (s := ball (0 : Fin (k + 1) → ℂ) R)) 0)
    · simp only [hF, cons_val_succ, mulVec, dotProduct]
      exact DifferentiableOn.fun_sum fun l _ => (differentiableOn_pi.1 hγ l).const_mul _
  have hFa := analyticOnNhd_of_differentiableOn isOpen_ball hFd
  set e := (LinearEquiv.ofBijective
    (fderiv ℂ F s : (Fin (k + 1) → ℂ) →ₗ[ℂ] Fin (k + 1) → ℂ) hbij).toContinuousLinearEquiv
  have he : (e : (Fin (k + 1) → ℂ) →L[ℂ] Fin (k + 1) → ℂ) = fderiv ℂ F s := by ext1 x; rfl
  have hst : HasStrictFDerivAt F (e : (Fin (k + 1) → ℂ) →L[ℂ] Fin (k + 1) → ℂ) s := by
    rw [he]; exact (hFa s hs).hasStrictFDerivAt
  have hV : ∀ᶠ t in 𝓝 s, (t ∈ ball (0 : Fin (k + 1) → ℂ) R ∧ fderiv ℂ F t ∈
      Set.range ((↑) : ((Fin (k + 1) → ℂ) ≃L[ℂ] (Fin (k + 1) → ℂ)) → _)) ∧
      t ∈ (hst.toOpenPartialHomeomorph F).source :=
    (Filter.Eventually.and (isOpen_ball.mem_nhds hs) ((hFa s hs).fderiv.continuousAt.preimage_mem_nhds
      (ContinuousLinearEquiv.isOpen.mem_nhds ⟨e, he⟩))).and
      ((hst.toOpenPartialHomeomorph F).open_source.mem_nhds hst.mem_toOpenPartialHomeomorph_source)
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
  set Ψ := (hst.toOpenPartialHomeomorph F).restrOpen (ball s ε) isOpen_ball
  have hΨs : Ψ.source = (hst.toOpenPartialHomeomorph F).source ∩ ball s ε :=
    OpenPartialHomeomorph.restrOpen_source _ _ _
  have hsΨ : s ∈ Ψ.source := hΨs ▸ ⟨hst.mem_toOpenPartialHomeomorph_source, mem_ball_self hε⟩
  have hsrc : ∀ t ∈ Ψ.source, t ∈ ball 0 R ∧
      ∃ e' : (Fin (k + 1) → ℂ) ≃L[ℂ] (Fin (k + 1) → ℂ), HasFDerivAt Ψ (e' : _ →L[ℂ] _) t := by
    intro t ht
    obtain ⟨⟨htR, e', he'⟩, -⟩ := hεV (hΨs ▸ ht).2
    refine ⟨htR, e', ?_⟩
    rw [he']; exact (hFa t htR).differentiableAt.hasFDerivAt
  obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.1 Ψ.open_target (F s) (Ψ.map_source hsΨ)
  set p : (Fin 1 → ℂ) → Fin (k + 1) → ℂ := fun τ => vecCons (s 0 + τ 0) (L *ᵥ γ s) with hp
  have hpT : ∀ τ ∈ ball (0 : Fin 1 → ℂ) r, p τ ∈ Ψ.target := by
    intro τ hτ
    refine hrT ((dist_pi_lt_iff hr).2 fun i => Fin.cases ?_ (fun j => ?_) i)
    · simpa [hp, hF, dist_eq_norm] using (norm_le_pi_norm τ 0).trans_lt (mem_ball_zero_iff.1 hτ)
    · simpa [hp, hF] using hr
  refine ⟨r, hr, fun τ => Ψ.symm (p τ), fun τ hτ => ?_, ?_, fun τ hτ => ?_, ?_⟩
  · have hpd : Differentiable ℂ p := differentiable_pi.2 fun i => Fin.cases
      (by simpa [hp] using (differentiable_const (s 0)).add (differentiable_pi.1 differentiable_id 0))
      (fun j => by simp [hp]) i
    obtain ⟨-, e', he'⟩ := hsrc _ (Ψ.map_target (hpT τ hτ))
    exact ((Ψ.hasFDerivAt_symm (hpT τ hτ) he').differentiableAt.comp τ
      (hpd τ)).differentiableWithinAt
  · have h0 : p 0 = F s := by simp [hp, hF]
    show Ψ.symm (p 0) = s
    rw [h0]; exact Ψ.left_inv hsΨ
  · have h2 : F (Ψ.symm (p τ)) = p τ := Ψ.right_inv (hpT τ hτ)
    refine ⟨(hsrc _ (Ψ.map_target (hpT τ hτ))).1, ?_, ?_⟩
    · simpa [hF, hp] using congrFun h2 0
    · simpa [hF, hp] using congrArg Fin.tail h2
  · refine ⟨Ψ.source ∩ {t | ‖t 0 - s 0‖ < r}, Filter.inter_mem (Ψ.open_source.mem_nhds hsΨ)
      ((isOpen_lt ((continuous_apply 0).sub continuous_const).norm continuous_const).mem_nhds
        (by simpa using hr)), ?_⟩
    rintro t ⟨ht, htr⟩ hL
    refine ⟨fun _ => t 0 - s 0, by simpa [pi_norm_const] using htr, ?_⟩
    have hpt : p (fun _ => t 0 - s 0) = F t := by simp [hp, hF, hL]
    dsimp only
    rw [hpt]; exact Ψ.left_inv ht
end GroundTheory.Heights₂.Heights.ImplicitCurve
