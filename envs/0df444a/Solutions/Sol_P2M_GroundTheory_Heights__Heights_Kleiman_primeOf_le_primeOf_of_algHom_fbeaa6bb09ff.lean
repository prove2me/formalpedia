-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_primeOf_le_primeOf_of_algHom_fbeaa6bb09ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:35:10.366461+00:00
-- url     : https://prove2.me/submissions/831d6685-3611-4c10-a45e-62bb57839288

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_mem_primeOf_077b7ab281b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {x : Fin (N + 1) → Ω} {j : Fin (N + 1)} (hj : x j ≠ 0)
    (ψ : chartRing k x (singleChart hj) →ₐ[k] K') :
    primeOf (S := k) x ≤ primeOf (S := k) (fun i => ψ (ratio hj i)) := by
  have key : ∀ {B : Type w} [CommRing B] [Algebra k B] (φ : chartRing k x (singleChart hj) →ₐ[k] B)
      (g : Poly k N), φ (aeval (ratio (S := k) hj) g) = aeval (fun i => φ (ratio hj i)) g := by
    intro B _ _ φ g
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  intro f hf
  have hcomp : ∀ d, homogeneousComponent d f ∈ primeOf (S := k) (fun i => ψ (ratio hj i)) := by
    intro d
    have hg := homogeneousComponent_isHomogeneous d f
    have h0 : aeval x (homogeneousComponent d f) = 0 :=
      (mem_primeOf_of_isHomogeneous x hg).mp (homogeneousComponent_mem_primeOf x hf d)
    rw [mem_primeOf_of_isHomogeneous _ hg, ← key]
    have hval : aeval (ratio (S := k) hj) (homogeneousComponent d f) = 0 := by
      apply Subtype.ext
      have := key (chartRing k x (singleChart hj)).val (homogeneousComponent d f)
      simp only [Subalgebra.coe_val] at this
      rw [this, ZeroMemClass.coe_zero]
      change aeval (fun l => x l / x j) (homogeneousComponent d f) = 0
      rw [aeval_div_of_isHomogeneous hg j, h0, zero_div]
    rw [hval, map_zero]
  rw [← sum_homogeneousComponent f]
  exact Ideal.sum_mem _ fun d _ => hcomp d
end GroundTheory.Heights₂.Heights.Kleiman
