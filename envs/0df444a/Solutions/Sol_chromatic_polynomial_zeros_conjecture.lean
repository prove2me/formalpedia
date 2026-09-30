-- Prove2me | solution 1 for chromatic_polynomial_zeros_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:34:54.872769+00:00
-- url     : https://prove2.me/submissions/7b656256-dca5-4b19-94c5-533cbd74a764

import Mathlib

set_option autoImplicit false

namespace ChromaticCounting

universe u v
variable {V : Type u} {K : Type v}

def ProperPartition (G : SimpleGraph V) :=
  {s : Setoid V // ∀ x y, G.Adj x y → ¬ s.r x y}

def ProperColoring (G : SimpleGraph V) (K : Type v) :=
  {f : V → K // ∀ x y, G.Adj x y → f x ≠ f y}

def kernel (G : SimpleGraph V) (f : ProperColoring G K) : ProperPartition G :=
  ⟨Setoid.ker f.val, f.property⟩

def paint (s : Setoid V) (e : Quotient s ↪ K) : V → K :=
  fun x => e (Quotient.mk s x)

lemma kernel_paint (s : Setoid V) (e : Quotient s ↪ K) : Setoid.ker (paint s e) = s := by
  ext x y
  exact e.injective.eq_iff.trans Quotient.eq

def paintProper (G : SimpleGraph V) (s : ProperPartition G)
    (e : Quotient s.val ↪ K) : ProperColoring G K :=
  ⟨paint s.val e, fun x y hxy heq =>
    s.property x y hxy (Quotient.exact (e.injective heq))⟩

lemma kernel_paintProper (G : SimpleGraph V) (s : ProperPartition G)
    (e : Quotient s.val ↪ K) : kernel G (paintProper G s e) = s := by
  apply Subtype.ext
  exact kernel_paint s.val e

noncomputable def fiberEquiv (G : SimpleGraph V) (s : ProperPartition G) :
    {f : ProperColoring G K // kernel G f = s} ≃ (Quotient s.val ↪ K) where
  toFun f := by
    have hker : Setoid.ker f.val.val = s.val := congrArg Subtype.val f.property
    refine ⟨Quotient.lift f.val.val (fun x y hxy => ?_), ?_⟩
    · exact (show s.val ≤ Setoid.ker f.val.val from hker.ge) hxy
    · exact (Setoid.lift_injective_iff_ker_eq_of_le hker.ge).2 hker
  invFun e := ⟨paintProper G s e, kernel_paintProper G s e⟩
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    rfl
  right_inv e := by
    apply Function.Embedding.ext
    intro q
    induction q using Quotient.inductionOn
    rfl

noncomputable local instance setoidFintype [Fintype V] : Fintype (Setoid V) := by
  classical
  exact Fintype.ofInjective (fun s : Setoid V => s.r) (fun s t h => by
    ext x y
    exact iff_of_eq (congrFun (congrFun h x) y))

noncomputable local instance partitionFintype [Fintype V] (G : SimpleGraph V) :
    Fintype (ProperPartition G) := by
  classical
  unfold ProperPartition
  infer_instance

noncomputable local instance coloringFintype [Fintype V] [Fintype K] (G : SimpleGraph V) :
    Fintype (ProperColoring G K) := by
  classical
  unfold ProperColoring
  infer_instance

lemma card_colorings [Fintype V] [Fintype K] (G : SimpleGraph V) :
    Fintype.card (ProperColoring G K) =
      ∑ s : ProperPartition G, (Fintype.card K).descFactorial (Nat.card (Quotient s.val)) := by
  classical
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv (kernel G (K := K))).symm
  rw [Fintype.card_sigma] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro s _
  let := Fintype.ofFinite (Quotient s.val)
  rw [Fintype.card_congr (fiberEquiv G s), Fintype.card_embedding_eq, Nat.card_eq_fintype_card]

noncomputable def countingPolynomial [Fintype V] (G : SimpleGraph V) : Polynomial ℤ :=
  ∑ s : ProperPartition G, descPochhammer ℤ (Nat.card (Quotient s.val))

lemma countingPolynomial_eval [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (countingPolynomial G).eval (k : ℤ) = (Nat.card (ProperColoring G (Fin k)) : ℤ) := by
  classical
  rw [Nat.card_eq_fintype_card, card_colorings]
  simp [countingPolynomial, Polynomial.eval_finsetSum, descPochhammer_eval_eq_descFactorial]

end ChromaticCounting

theorem solution
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ (P : Polynomial ℤ), ∀ k : ℤ, 0 ≤ k →
      (P.eval k).toNat = {col : Fin n → Fin k.toNat |
        ∀ v w : Fin n, G.Adj v w → col v ≠ col w}.ncard := by
  classical
  refine ⟨ChromaticCounting.countingPolynomial G, fun k hk => ?_⟩
  have h := ChromaticCounting.countingPolynomial_eval G k.toNat
  rw [Int.toNat_of_nonneg hk] at h
  rw [h, Int.toNat_natCast]
  rfl

#print axioms solution
