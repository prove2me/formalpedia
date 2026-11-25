-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootPointConjugation_homog_vanish_73dd4aea5fe2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:27:44.971272+00:00
-- url     : https://prove2.me/submissions/8cbf74d9-5009-4fe4-9bb9-c3aa92d025f8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootPointConj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootPointConjugation_aeval_mul_monomial_c5929ecdffff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootPointConjugation_sum_homog_2122288929cc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_anchor_minor_b307d35ccb1e


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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.RootPointConjugation
namespace GroundTheory.Heights₂.Heights.RootPointConjugation
theorem _root_.solution {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ)
    (z : (Σ _ : Fin f, PlIdx j m) → ℂ) (hz : z ∈ mcPts (rootPointIdeal ζ)) (τ : Fin f)
    (u : PlIdx j m → ℂ) (hu : ∀ I, z ⟨τ, I⟩ = z ⟨τ, plAnchor j m⟩ * u I)
    (Q : MvPolynomial (PlIdx j m) ℤ) (hQ : aeval (fun I => rootCoord ζ ⟨τ, I⟩) Q = 0) :
    z ⟨τ, plAnchor j m⟩ ^ Q.totalDegree * aeval u Q = 0 := by
  classical
  have hS : ∀ μ ∈ Q.support, (μ.sum fun _ e => e) ≤ Q.totalDegree := fun μ hμ => le_totalDegree hμ
  set H : MRing (plBlocks f j m) := ∑ μ ∈ Q.support,
    X ⟨τ, plAnchor j m⟩ ^ (Q.totalDegree - μ.sum fun _ e => e) *
      rename (Sigma.mk τ) (monomial μ (coeff μ Q)) with hH
  have hmem : H ∈ rootPointIdeal ζ := by
    show mConeMap (rootCoord ζ) H = 0
    have hC : ∀ P : MvPolynomial (PlIdx j m) ℤ,
        aeval (fun I => (C (rootCoord ζ ⟨τ, I⟩) : MvPolynomial (Fin f) ℂ)) P =
          C (aeval (fun I => rootCoord ζ ⟨τ, I⟩) P) := by
      intro P
      induction P using MvPolynomial.induction_on <;> simp_all
    have hcomp : (fun p => C (rootCoord ζ p) * (X p.1 : MvPolynomial (Fin f) ℂ)) ∘ Sigma.mk τ =
        fun I => X τ * C (rootCoord ζ ⟨τ, I⟩) := by
      funext I; simp [mul_comm]
    have ha : rootCoord ζ ⟨τ, plAnchor j m⟩ = 1 := anchor_minor j m (ζ τ)
    have hsc : ∀ (μ : PlIdx j m →₀ ℕ) (c : ℤ),
        aeval (fun I => X τ * (C (rootCoord ζ ⟨τ, I⟩) : MvPolynomial (Fin f) ℂ)) (monomial μ c) =
          X τ ^ (μ.sum fun _ e => e) * aeval (fun I => C (rootCoord ζ ⟨τ, I⟩)) (monomial μ c) :=
      fun μ c => aeval_mul_monomial _ _ μ c
    simp only [hH, mConeMap, map_sum, map_mul, map_pow, aeval_X, aeval_rename, hcomp,
      hsc, hC, ha, map_one, one_mul]
    rw [sum_homog _ _ hS, ← map_sum, ← map_sum, ← as_sum, hQ, map_zero, mul_zero]
  have hE := hz.2 H hmem
  rw [eval_map, ← algebraMap_int_eq, ← aeval_def] at hE
  have hcomp2 : z ∘ Sigma.mk τ = fun I => z ⟨τ, plAnchor j m⟩ * u I := funext hu
  simp only [hH, map_sum, map_mul, map_pow, aeval_X, aeval_rename, hcomp2, aeval_mul_monomial] at hE
  rwa [sum_homog _ _ hS, ← map_sum, ← as_sum] at hE
end GroundTheory.Heights₂.Heights.RootPointConjugation
