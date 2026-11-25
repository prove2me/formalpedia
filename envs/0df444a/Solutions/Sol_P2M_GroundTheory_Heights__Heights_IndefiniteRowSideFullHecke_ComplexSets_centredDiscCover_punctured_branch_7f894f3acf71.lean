-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_centredDiscCover_punctured_branch_7f894f3acf71
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:52.208179+00:00
-- url     : https://prove2.me/submissions/3af936a4-c5cd-43ba-902a-14be65740c4c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCentredDiscCoverCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedCoverCycles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCentredDiscCoverCurve

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
open Topology Filter Metric Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (hPCC : PuncturedCoverCycles.Statement)
    {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {w : σ → ℂ} {p : (σ → ℂ) →L[ℂ] ℂ} {ρ : ℝ} {N : ℕ}
    (hY : IsCentredDiscCover Y w p ρ N) :
    ∃ (δ : ℝ) (k : ℕ) (φ : ℂ → σ → ℂ), 0 < δ ∧ δ ≤ 1 ∧ 1 ≤ k ∧
      DifferentiableOn ℂ φ (ball 0 δ \ {0}) ∧ Set.InjOn φ (ball 0 δ \ {0}) ∧
      ∀ s ∈ ball (0 : ℂ) δ \ {0}, φ s ∈ Y ∧ p (φ s) = p w + s ^ k := by
  obtain ⟨hwY, hN, hmaps, huniq, hcard, -, hsec⟩ := hY
  have hρ : 0 < ρ := dist_nonneg.trans_lt (hmaps hwY)
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let Φ : (Fin (Fintype.card σ) → ℂ) ≃L[ℂ] (σ → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ e).toContinuousLinearEquiv
  let L : (Fin (Fintype.card σ) → ℂ) →L[ℂ] (Fin 1 → ℂ) :=
    ContinuousLinearMap.pi fun _ => p.comp (Φ : (Fin (Fintype.card σ) → ℂ) →L[ℂ] (σ → ℂ))
  let A : Matrix (Fin (0 + 1)) (Fin (Fintype.card σ)) ℂ :=
    LinearMap.toMatrix' (L : (Fin (Fintype.card σ) → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))
  have hA : ∀ z, A *ᵥ z = fun _ => p (Φ z) := fun z => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have hpT : ∀ z, p (w + Φ z) = p w + p (Φ z) := fun z => map_add p w (Φ z)
  have hT : ∀ x, w + Φ (Φ.symm (x - w)) = x := fun x => by simp
  have hone : ∀ (y : Fin (0 + 1) → ℂ) (t : ℂ), t = y 0 → (fun _ => t) = y := fun y t ht => by
    funext i
    rw [show i = 0 from Subsingleton.elim (α := Fin 1) _ _, ht]
  let X : Set (Fin (Fintype.card σ) → ℂ) := {z | w + Φ z ∈ Y ∧ p (Φ z) ≠ 0}
  obtain ⟨m, ord, ψ, δ, hδ, hδ1, hsum, hord, hdiff, hmap, hinj, -, -⟩ :=
    hPCC (Fintype.card σ) 0 N A 0 ρ X hρ rfl
      (fun x hx => by
        rw [hA, dist_zero_right, pi_norm_const]
        refine ⟨?_, hx.2⟩
        have := hmaps hx.1
        rwa [mem_ball, dist_eq_norm, hpT, add_sub_cancel_left] at this)
      (fun y hy hy0 => by
        have hyρ : p w + y 0 ∈ ball (p w) ρ := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
          exact (norm_le_pi_norm y 0).trans_lt (by rwa [dist_zero_right] at hy)
        rw [← hcard _ hyρ (by simpa using hy0), ← ((add_right_injective w).comp Φ.injective).injOn.encard_image]
        congr 1
        ext x
        constructor
        · rintro ⟨z, ⟨⟨hzY, -⟩, hzy⟩, rfl⟩
          refine ⟨hzY, ?_⟩
          rw [Function.comp_apply, hpT, ← congrFun ((hA z).symm.trans hzy) 0]
        · rintro ⟨hxY, hxp⟩
          refine ⟨Φ.symm (x - w), ⟨⟨by rwa [hT], ?_⟩, ?_⟩, hT x⟩
          · simpa [hxp] using hy0
          · rw [hA]
            exact hone y _ (by simp [hxp]))
      (fun x hx => by
        obtain ⟨O₀, V₀, g₀, hO₀, hV₀, hxV₀, hg₀, hpg₀, hYV⟩ :=
          hsec (w + Φ x) hx.1 (by rw [hpT]; simpa using hx.2)
        have hsec' : ∀ z, w + Φ z ∈ Y ∩ V₀ → p w + p (Φ z) ∈ O₀ ∧ g₀ (p w + p (Φ z)) = w + Φ z := by
          intro z hz
          rw [hYV] at hz
          obtain ⟨t, ht, hgt⟩ := hz
          have : t = p w + p (Φ z) := by rw [← hpT, ← hgt, hpg₀ t ht]
          subst this
          exact ⟨ht, hgt⟩
        obtain ⟨hxO, hgx⟩ := hsec' x ⟨hx.1, hxV₀⟩
        refine ⟨{y | p w + y 0 ∈ O₀ ∧ y 0 ≠ 0}, {z | w + Φ z ∈ V₀ ∧ p (Φ z) ≠ 0},
          fun y => Φ.symm (g₀ (p w + y 0) - w),
          (hO₀.preimage (continuous_const.add (continuous_apply 0))).inter
            (isOpen_ne_fun (continuous_apply 0) continuous_const),
          by rw [hA]; exact ⟨hxO, hx.2⟩,
          (hV₀.preimage (continuous_const.add Φ.continuous)).inter
            (isOpen_ne_fun (p.continuous.comp Φ.continuous) continuous_const),
          ⟨hxV₀, hx.2⟩, ?_, by rw [hA]; simp [hgx], fun y hy => ?_, ?_⟩
        · exact Φ.symm.differentiable.comp_differentiableOn
            ((hg₀.comp ((differentiableOn_const _).add (differentiable_apply 0).differentiableOn)
              fun y hy => hy.1).sub_const w)
        · rw [hA]
          refine hone y _ ?_
          simp [hpg₀ _ hy.1]
        · ext z
          constructor
          · rintro ⟨⟨hzY, hz0⟩, hzV, -⟩
            obtain ⟨hzO, hgz⟩ := hsec' z ⟨hzY, hzV⟩
            exact ⟨fun _ => p (Φ z), ⟨hzO, hz0⟩, by simp [hgz]⟩
          · rintro ⟨y, ⟨hyO, hy0⟩, rfl⟩
            have hw : w + Φ (Φ.symm (g₀ (p w + y 0) - w)) = g₀ (p w + y 0) := hT _
            have hp : p (Φ (Φ.symm (g₀ (p w + y 0) - w))) = y 0 := by simp [hpg₀ _ hyO]
            have hmem : g₀ (p w + y 0) ∈ Y ∩ V₀ := by rw [hYV]; exact ⟨_, hyO, rfl⟩
            show (w + Φ (Φ.symm (g₀ (p w + y 0) - w)) ∈ Y ∧ p (Φ (Φ.symm (g₀ (p w + y 0) - w))) ≠ 0) ∧
              (w + Φ (Φ.symm (g₀ (p w + y 0) - w)) ∈ V₀ ∧ p (Φ (Φ.symm (g₀ (p w + y 0) - w))) ≠ 0)
            rw [hw, hp]
            exact ⟨⟨hmem.1, hy0⟩, hmem.2, hy0⟩)
  obtain ⟨b⟩ : Nonempty (Fin m) := by
    rcases m with _ | m
    · simp at hsum
      omega
    · exact ⟨0⟩
  have hpunct : ∀ s ∈ ball (0 : ℂ) δ \ {0},
      (fun _ => s) ∈ ball (0 : Fin (0 + 1) → ℂ) δ ∩ {t | t 0 ≠ 0} := fun s hs =>
    ⟨by rw [mem_ball, dist_zero_right, pi_norm_const]; exact mem_ball_zero_iff.1 hs.1, hs.2⟩
  refine ⟨δ, ord b, fun s => w + Φ (ψ b fun _ => s), hδ, hδ1, hord b, ?_, ?_, fun s hs => ?_⟩
  · exact (differentiableOn_const w).add (Φ.differentiable.comp_differentiableOn
      ((hdiff b).comp (differentiable_pi.2 fun _ => differentiable_id).differentiableOn hpunct))
  · intro s hs s' hs' hss'
    have := hinj b (hpunct s hs) (hpunct s' hs') (Φ.injective (add_left_cancel hss'))
    exact congrFun this 0
  · obtain ⟨hX, hAψ⟩ := hmap b _ (hpunct s hs)
    refine ⟨hX.1, ?_⟩
    rw [hpT]
    have := congrFun ((hA _).symm.trans hAψ) 0
    simp only [Function.update_self] at this
    rw [this]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
