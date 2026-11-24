-- Prove2me | solution 1 for PI.GreenLabelMapW.conj_roots
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:58.808417+00:00
-- url     : https://prove2.me/submissions/6e5e25e2-a957-4347-947b-c5c02aaa0ce0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IntermediateField
noncomputable section
open PI PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K]
namespace PI.GreenLabelMapW
theorem _root_.solution {P : K[X]} (hm : P.Monic) (hi : Irreducible P) {w : AlgebraicClosure K}
    (hw : aeval w P = 0) (f : AlgebraicClosure K → AlgebraicClosure K)
    (hf : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure K),
      f (σ x) = σ (f x)) (y : AlgebraicClosure K) :
    aeval y (minpoly K (f w)) = 0 ↔ ∃ r, aeval r P = 0 ∧ f r = y := by
  have halg : ∀ z : AlgebraicClosure K, IsAlgebraic K z := fun z => Algebra.IsAlgebraic.isAlgebraic z
  have hmin : P = minpoly K w := minpoly.eq_of_irreducible_of_monic hi hw hm
  constructor
  · intro hy
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root (halg (f w)) hy
    refine ⟨σ.symm w, ?_, ?_⟩
    · simpa [hw] using Polynomial.aeval_algHom_apply (σ.symm : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) w P
    · rw [hf, ← hσ, AlgEquiv.symm_apply_apply]
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root (halg w) (by rw [← hmin]; exact hr)
    rw [← hσ, hf, show minpoly K (σ (f r)) = minpoly K (f r) from
      minpoly.algHom_eq (σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) σ.injective (f r)]
    exact minpoly.aeval K (f r)
end PI.GreenLabelMapW
