-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_proof_of_frame_2fb63f20aef4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:19:55.8118+00:00
-- url     : https://prove2.me/submissions/0cdcbac6-c196-4995-89f3-e97c08c1ce1f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StJacobianRankOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameJacobianGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PJacobianRankGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PConormalGenerationGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PJacobianRankOffHypersurface
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_finrank_of_generators_fbbde75efc83
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_exists_fin_ec031f113fa3

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace JacobianRankOffHypersurface
theorem _root_.solution (hF : FrameJacobianGeneric.Statement) :
    JacobianRankOffHypersurface.Statement := by
  intro σ _ Q d r q t hQ hd hqQ htQ hgen
  set n := Fintype.card σ
  set e : σ ≃ Fin n := Fintype.equivFin σ
  set φ : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ := renameEquiv ℂ e.symm
  set J : Ideal (MvPolynomial (Fin n) ℂ) := Q.comap φ
  have hJ : J.IsPrime := Ideal.IsPrime.comap _
  have hφ : ∀ (x : σ → ℂ) (p : MvPolynomial (Fin n) ℂ), eval x (φ p) = eval (x ∘ e.symm) p := fun x p ↦ by
    simp [φ, eval_rename]
  have hJd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
    rw [← hd]
    refine (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv Q J φ.toRingEquiv.symm ?_)).symm
    exact (Ideal.map_symm (I := Q) φ.toRingEquiv).symm
  obtain ⟨I₀, f, s, δ, hcard, hfJ, hsJ, hδJ, hsgen, hlin⟩ :=
    JacobianRankOffHypersurface.exists_fin hF J hJ hJd
  have hfQ : ∀ k, φ (f k) ∈ Q := fun k ↦ Ideal.mem_comap.mp (hfJ k)
  have hsQ : φ s ∉ Q := fun h ↦ hsJ (Ideal.mem_comap.mpr h)
  have hδQ : φ δ ∉ Q := fun h ↦ hδJ (Ideal.mem_comap.mpr h)
  have hs : ∀ p ∈ Q, φ s * p ∈ Ideal.span (Set.range fun k ↦ φ (f k)) := by
    intro p hp
    have hp' : φ.symm p ∈ J := Ideal.mem_comap.mpr (by rwa [AlgEquiv.apply_symm_apply])
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hsgen _ hp')
    refine Ideal.mem_span_range_iff_exists_fun.mpr ⟨fun k ↦ φ (c k), ?_⟩
    have := congrArg φ hc
    rw [map_sum, map_mul, AlgEquiv.apply_symm_apply] at this
    simpa [map_mul] using this
  have hδ : ∀ w : σ → ℂ, eval w (φ δ) ≠ 0 →
      LinearIndependent ℂ fun k x ↦ eval w (pderiv x (φ (f k))) := by
    intro w hw
    rw [hφ] at hw
    have hL := (hlin _ hw).map' (LinearMap.funLeft ℂ ℂ e)
      (LinearMap.ker_eq_bot.mpr (LinearMap.funLeft_injective_of_surjective _ _ _ e.surjective))
    have hfam : (fun k x ↦ eval w (pderiv x (φ (f k)))) =
        (LinearMap.funLeft ℂ ℂ e) ∘ fun k l ↦ eval (w ∘ e.symm) (pderiv l (f k)) := by
      funext k x
      simp only [Function.comp_apply, LinearMap.funLeft_apply]
      have hx : pderiv x (φ (f k)) = φ (pderiv (e x) (f k)) := by
        have := pderiv_rename (R := ℂ) e.symm.injective (e x) (f k)
        rw [Equiv.symm_apply_apply] at this
        exact this
      rw [hx, hφ]
    rw [hfam]
    exact hL
  have hμQ : φ s * t * φ δ ∉ Q := by
    intro h
    rcases hQ.mem_or_mem h with h | h
    · rcases hQ.mem_or_mem h with h | h
      · exact hsQ h
      · exact htQ h
    · exact hδQ h
  exact ⟨φ s * t * φ δ, hμQ, fun w hw hμ ↦
    JacobianRankOffHypersurface.finrank_of_generators Q d r q t hqQ hgen (fun k ↦ φ (f k)) (φ s) (φ δ) hfQ hs hδ
      hcard w hw hμ⟩
end JacobianRankOffHypersurface
end GroundTheory.Heights₂.Heights
