-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.restBlockSubst_isMultiHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:14:35.791948+00:00
-- url     : https://prove2.me/submissions/43e2cf90-b1a6-4df3-a8fa-70f3d308346b

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
    {g : MvPolynomial (Fin (B + 1) × Fin n) ℂ} (hg : IsMultiHomogeneous a g) (x : Fin n → ℂ) :
    IsMultiHomogeneous (fun b => a b.succ) (aeval (lh0Rest x) g) := by
  classical
  have hW : IsWeightedHomogeneous (fun p : Fin B × Fin n => (Pi.single p.1 1 : Fin B → ℕ))
      (aeval (lh0Rest x) g) (fun b => a b.succ) := by
    refine aeval_whom_lemma _ (lh0Rest x)
      (fun p => (Fin.cons (0 : Fin B → ℕ) (fun b => Pi.single b 1) :
        Fin (B + 1) → Fin B → ℕ) p.1) ?_ g _ ?_
    · rintro ⟨b, j⟩
      refine Fin.cases ?_ (fun b => ?_) b
      · simpa [lh0Rest] using isWeightedHomogeneous_C
          (fun p : Fin B × Fin n => (Pi.single p.1 1 : Fin B → ℕ)) (x j)
      · simpa [lh0Rest] using isWeightedHomogeneous_X ℂ
          (fun p : Fin B × Fin n => (Pi.single p.1 1 : Fin B → ℕ)) (b, j)
    · intro s hs
      funext b
      rw [Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
        rw [Finsupp.notMem_support_iff.mp hi, zero_smul], Finset.sum_apply,
        Fintype.sum_prod_type, Fin.sum_univ_succ, ← hg s hs b.succ]
      simp only [Fin.cons_zero, Fin.cons_succ, smul_zero, Pi.zero_apply, Finset.sum_const_zero,
        zero_add]
      rw [Finset.sum_eq_single b]
      · simp
      · intro c _ hc
        simp [Pi.single_apply, Ne.symm hc]
      · simp
  intro s hs b
  have hb := congrFun (hW (MvPolynomial.mem_support_iff.mp hs)) b
  refine Eq.trans ?_ hb
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply,
    Finset.sum_subset (s₁ := s.support) (Finset.subset_univ _) fun i _ hi => by
      rw [Finsupp.notMem_support_iff.mp hi, zero_smul, Pi.zero_apply],
    Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    simp [Pi.single_apply, Ne.symm hc]
  · simp
end ReciprocityTheory.MultiplicativeHeights
