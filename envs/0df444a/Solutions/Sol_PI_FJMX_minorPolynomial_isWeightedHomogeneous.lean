-- Prove2me | solution 1 for PI.FJMX.minorPolynomial_isWeightedHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:07.623251+00:00
-- url     : https://prove2.me/submissions/094c46d8-d868-4222-a63c-0d1c7dbbfe96

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.FJMX
variable {R : Type*} [CommRing R] {σ : Type*}
namespace PI.FJMX
theorem _root_.solution {k : ℕ} (g : Fin k → Fin k → σ) (w : σ → ℕ) (u v : Fin k → ℕ)
    (hw : ∀ i j, w (g i j) = u i + v j) :
    IsWeightedHomogeneous w (minorPolynomial R g) (∑ i, u i + ∑ j, v j) := by
  classical
  rw [minorPolynomial, Matrix.det_apply']
  apply IsWeightedHomogeneous.sum
  intro τ _
  have hp : IsWeightedHomogeneous w
      (∏ i, (Matrix.of fun i j => (X (g i j) : MvPolynomial σ R)) (τ i) i)
      (∑ i, w (g (τ i) i)) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => isWeightedHomogeneous_X _ _ _
  have hc : ∑ i, w (g (τ i) i) = ∑ i, u i + ∑ j, v j := by
    simp only [hw, Finset.sum_add_distrib]
    congr 1
    exact Equiv.sum_comp τ u
  rw [hc] at hp
  have h0 : IsWeightedHomogeneous w (((Equiv.Perm.sign τ : ℤ) : MvPolynomial σ R)) 0 := by
    rw [← map_intCast (C : R →+* MvPolynomial σ R)]
    exact isWeightedHomogeneous_C _ _
  have := h0.mul hp
  rw [zero_add] at this
  exact this
end PI.FJMX
