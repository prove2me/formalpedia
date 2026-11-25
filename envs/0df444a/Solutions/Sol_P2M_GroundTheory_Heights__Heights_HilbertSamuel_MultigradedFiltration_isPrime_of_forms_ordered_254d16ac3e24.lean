-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isPrime_of_forms_ordered_254d16ac3e24
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:29.009355+00:00
-- url     : https://prove2.me/submissions/8e5a7b1e-025e-40f1-98e3-15e96a22ee38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedFiltration

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
theorem _root_.solution {σ L : Type*} [AddCommMonoid L] [LinearOrder L]
    [IsOrderedCancelAddMonoid L] (w : σ → L) (q : Ideal (MvPolynomial σ F))
    (hq : ∀ r ∈ q, ∀ i, weightedHomogeneousComponent w i r ∈ q) (hne : q ≠ ⊤)
    (h : ∀ a b : MvPolynomial σ F, (∃ i, IsWeightedHomogeneous w a i) →
      (∃ j, IsWeightedHomogeneous w b j) → a * b ∈ q → a ∈ q ∨ b ∈ q) :
    q.IsPrime := by
  letI := weightedGradedAlgebra F w
  have hH : q.IsHomogeneous (weightedHomogeneousSubmodule F w) := by
    intro i r hr
    have e : (DirectSum.decompose (weightedHomogeneousSubmodule F w) r i : MvPolynomial σ F) =
        weightedHomogeneousComponent w i r := weightedDecomposition.decompose'_apply F w r i
    rw [e]
    exact hq r hr i
  refine hH.isPrime_of_homogeneous_mem_or_mem hne ?_
  rintro a b ⟨i, hi⟩ ⟨j, hj⟩ hab
  exact h a b ⟨i, hi⟩ ⟨j, hj⟩ hab
end GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
