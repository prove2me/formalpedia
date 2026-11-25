-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_grad_mem_span_406acfd04172
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:57:09.298622+00:00
-- url     : https://prove2.me/submissions/d75ef5a9-9945-499e-93c9-6d982f1fed52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StJacobianRankOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameJacobianGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PJacobianRankGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PConormalGenerationGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PJacobianRankOffHypersurface
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_eval_pderiv_sum_mul_8d82014868a9

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
theorem _root_.solution {σ ι : Type*} [Fintype ι] (w : σ → ℂ)
    (a p : MvPolynomial σ ℂ) (c g : ι → MvPolynomial σ ℂ) (hsum : ∑ k, c k * g k = a * p)
    (hg : ∀ k, eval w (g k) = 0) (hp : eval w p = 0) (ha : eval w a ≠ 0) :
    (fun x ↦ eval w (pderiv x p)) ∈
      Submodule.span ℂ (Set.range fun k x ↦ eval w (pderiv x (g k))) := by
  have key : (fun x ↦ eval w (pderiv x p)) =
      (eval w a)⁻¹ • ∑ k, eval w (c k) • (fun x ↦ eval w (pderiv x (g k))) := by
    funext x
    have h1 := congrArg (fun f ↦ eval w (pderiv x f)) hsum
    simp only [JacobianRankOffHypersurface.eval_pderiv_sum_mul w c g hg x, Derivation.leibniz, smul_eq_mul,
      map_add, map_mul, hp, zero_mul, add_zero] at h1
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, h1]
    rw [inv_mul_cancel_left₀ ha]
  rw [key]
  exact Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
end JacobianRankOffHypersurface
end GroundTheory.Heights₂.Heights
