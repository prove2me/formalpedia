-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.firstBlockSubst_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:27:47.101527+00:00
-- url     : https://prove2.me/submissions/c0204b3c-7bd7-4632-af86-81b9c1b777a0

import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory MvPolynomial
private theorem aeval_whom_lemma {σ τ : Type*} {M : Type*} [AddCommMonoid M] (w : τ → M)
    (v : σ → MvPolynomial τ ℂ) (d : σ → M) (hv : ∀ i, IsWeightedHomogeneous w (v i) (d i))
    (g : MvPolynomial σ ℂ) (m : M) (hg : ∀ s ∈ g.support, ∑ i ∈ s.support, s i • d i = m) :
    IsWeightedHomogeneous w (aeval v g) m := by
  classical
  rw [g.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun s hs => ?_
  rw [aeval_monomial, MvPolynomial.algebraMap_eq, ← hg s hs,
    ← zero_add (∑ i ∈ s.support, s i • d i), Finsupp.prod]
  exact (isWeightedHomogeneous_C w _).mul
    (IsWeightedHomogeneous.prod _ _ _ fun i _ => (hv i).pow _)
end ReciprocityTheory.MultiplicativeHeights
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {B n : ℕ} {a : Fin (B + 1) → ℕ}
    {g : MvPolynomial (Fin (B + 1) × Fin n) ℂ} (hg : IsMultiHomogeneous a g)
    (y : BlockSphere B n) : (aeval (lh0First y) g).IsHomogeneous (a 0) := by
  classical
  refine aeval_whom_lemma 1 (lh0First y)
    (fun p => (Fin.cons 1 (fun _ => 0) : Fin (B + 1) → ℕ) p.1) ?_ g (a 0) ?_
  · rintro ⟨b, j⟩
    refine Fin.cases ?_ (fun b => ?_) b
    · simpa [lh0First] using isWeightedHomogeneous_X ℂ (1 : Fin n → ℕ) j
    · simpa [lh0First] using isWeightedHomogeneous_C (1 : Fin n → ℕ) (blockPoint y (b, j))
  · intro s hs
    rw [Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
      rw [Finsupp.notMem_support_iff.mp hi, zero_smul], Fintype.sum_prod_type, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_eq_mul, mul_one, mul_zero,
      Finset.sum_const_zero, add_zero]
    exact hg s hs 0
end ReciprocityTheory.MultiplicativeHeights
