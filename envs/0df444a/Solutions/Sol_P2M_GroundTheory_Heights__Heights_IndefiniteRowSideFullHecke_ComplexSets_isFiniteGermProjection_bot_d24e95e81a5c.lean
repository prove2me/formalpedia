-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isFiniteGermProjection_bot_d24e95e81a5c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:31:46.224545+00:00
-- url     : https://prove2.me/submissions/7eab79a2-662e-4a84-8dbb-28475e82728f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionObjects

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
open Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] (w : σ → ℂ) :
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection w ⊥ A := by
  classical
  let e : (σ → ℂ) ≃L[ℂ] (Fin (Fintype.card σ) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ).symm).toContinuousLinearEquiv
  let A : (σ → ℂ) →L[ℂ] (Fin (Fintype.card σ) → ℂ) := e
  have hA : AnalyticAt ℂ (⇑A) w := A.analyticAt w
  have hB : AnalyticAt ℂ (⇑e.symm) (A w) := e.symm.analyticAt _
  have hBe : e.symm (A w) = w := e.symm_apply_apply w
  have back : ∀ φ : holGerms (A w), germPull e.symm hB hBe (germPull A hA rfl φ) = φ := fun φ =>
    germPull_germPull _ _ hA rfl hB hBe (fun y => e.apply_symm_apply y) φ
  have fwd : ∀ ψ : holGerms w, germPull A hA rfl (germPull e.symm hB hBe ψ) = ψ := fun ψ =>
    germPull_germPull _ _ hB hBe hA rfl (fun z => e.symm_apply_apply z) ψ
  refine ⟨Fintype.card σ, A, ?_, ?_, ?_⟩
  · intro φ hφ
    rw [Ideal.mem_bot] at hφ
    rw [← back φ, hφ, map_zero]
  · intro ψ
    refine ⟨MvPolynomial.C (germPull e.symm hB hBe ψ), ?_⟩
    rw [MvPolynomial.eval₂_C, fwd, sub_self]
    exact Ideal.zero_mem _
  · intro i
    have hc : AnalyticAt ℂ (fun y : Fin (Fintype.card σ) → ℂ => e.symm y i) (A w) :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).comp
        (e.symm : (Fin (Fintype.card σ) → ℂ) →L[ℂ] (σ → ℂ))).analyticAt _
    let c : holGerms (A w) := ⟨↑(fun y : Fin (Fintype.card σ) → ℂ => e.symm y i), _, hc, rfl⟩
    refine ⟨Polynomial.X - Polynomial.C c, Polynomial.monic_X_sub_C c, ?_⟩
    rw [Ideal.mem_bot, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero]
    apply Subtype.ext
    rw [germPull_coe _ hA rfl c _ rfl]
    show (↑(fun z : σ → ℂ => z i) : Germ (𝓝 w) ℂ) = ↑((fun y => e.symm y i) ∘ ⇑A)
    congr 1
    funext z
    simp [A]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
