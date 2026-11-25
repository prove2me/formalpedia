-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_finrank_of_generators_fbbde75efc83
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:44.003145+00:00
-- url     : https://prove2.me/submissions/408aa434-f41c-472e-aa34-9616be47e6ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StJacobianRankOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameJacobianGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PJacobianRankGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PConormalGenerationGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PJacobianRankOffHypersurface
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_grad_mem_span_406acfd04172

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
theorem _root_.solution {σ ι : Type*} [Fintype σ] [Fintype ι]
    (Q : Ideal (MvPolynomial σ ℂ)) (d r : ℕ) (q : Fin r → MvPolynomial σ ℂ) (t : MvPolynomial σ ℂ)
    (hqQ : ∀ j, q j ∈ Q) (hgen : ∀ p ∈ Q, ∃ i : ℕ, t ^ i * p ∈ Ideal.span (Set.range q))
    (f : ι → MvPolynomial σ ℂ) (s δ : MvPolynomial σ ℂ) (hfQ : ∀ k, f k ∈ Q)
    (hs : ∀ p ∈ Q, s * p ∈ Ideal.span (Set.range f))
    (hδ : ∀ w : σ → ℂ, eval w δ ≠ 0 → LinearIndependent ℂ fun k x ↦ eval w (pderiv x (f k)))
    (hcard : Fintype.card ι + d = Fintype.card σ) (w : σ → ℂ) (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn Q)
    (hμ : eval w (s * t * δ) ≠ 0) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range fun j x ↦ eval w (pderiv x (q j)))) + d =
      Fintype.card σ := by
  have hw' : ∀ p ∈ Q, eval w p = 0 := hw
  simp only [map_mul, mul_ne_zero_iff] at hμ
  obtain ⟨⟨hs0, ht0⟩, hδ0⟩ := hμ
  have heq : Submodule.span ℂ (Set.range fun j x ↦ eval w (pderiv x (q j))) =
      Submodule.span ℂ (Set.range fun k x ↦ eval w (pderiv x (f k))) := by
    apply le_antisymm
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro j
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hs (q j) (hqQ j))
      exact JacobianRankOffHypersurface.grad_mem_span w s (q j) c f hc (fun k ↦ hw' _ (hfQ k))
        (hw' _ (hqQ j)) hs0
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro k
      obtain ⟨i, hi⟩ := hgen (f k) (hfQ k)
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hi
      refine JacobianRankOffHypersurface.grad_mem_span w (t ^ i) (f k) c q hc (fun j ↦ hw' _ (hqQ j))
        (hw' _ (hfQ k)) ?_
      rw [map_pow]
      exact pow_ne_zero _ ht0
  rw [heq, finrank_span_eq_card (hδ w hδ0)]
  exact hcard
end JacobianRankOffHypersurface
end GroundTheory.Heights₂.Heights
