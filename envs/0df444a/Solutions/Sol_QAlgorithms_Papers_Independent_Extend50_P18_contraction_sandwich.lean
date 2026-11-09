-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P18.contraction_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T11:27:38.461494+00:00
-- url     : https://prove2.me/submissions/fdbd9dcf-dfce-413b-a538-84a592bc347d

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P18

noncomputable section

open scoped BigOperators Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

namespace Aux_P18cs
open QAlgorithms.Papers.Independent.Extend50.P18

theorem rev_rev {d k : ℕ} (w : Fin k → Fin d) : reverseWord (reverseWord w) = w := by
  funext l; simp [reverseWord]

theorem CL_apply (d r k : ℕ)
    (X : Matrix ((Fin r → Fin d) × (Fin k → Fin d)) ((Fin r → Fin d) × (Fin k → Fin d)) ℂ)
    (x y' : ContractionIndex d r k) :
    (pairedContraction d r k * liftInput X) x y' =
      (if x.2.1 = reverseWord x.2.2 then 1 else 0) *
        X (x.1, reverseWord y'.2.2) (y'.1, y'.2.1) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (x.1, (reverseWord y'.2.2, y'.2.2))]
  · simp only [pairedContraction, liftInput, Matrix.of_apply]
    by_cases h : x.2.1 = reverseWord x.2.2 <;> simp [h]
  · intro y _ hy
    simp only [pairedContraction, liftInput, Matrix.of_apply]
    by_cases h1 : x.1 = y.1 ∧ x.2.1 = reverseWord x.2.2 ∧ y.2.1 = reverseWord y.2.2
    · by_cases h2 : y.2.2 = y'.2.2
      · exfalso; apply hy
        obtain ⟨a, _, c⟩ := h1
        exact Prod.ext a.symm (Prod.ext (by rw [c, h2]) h2)
      · rw [if_neg h2]; simp
    · rw [if_neg h1]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

theorem lhs_apply (d r k : ℕ)
    (X : Matrix ((Fin r → Fin d) × (Fin k → Fin d)) ((Fin r → Fin d) × (Fin k → Fin d)) ℂ)
    (x z : ContractionIndex d r k) :
    (pairedContraction d r k * liftInput X * pairedContraction d r k) x z =
      (if x.2.1 = reverseWord x.2.2 then 1 else 0) *
        (if z.2.1 = reverseWord z.2.2 then 1 else 0) * QAlgorithms.traceRight X x.1 z.1 := by
  let f : (Fin k → Fin d) → ContractionIndex d r k := fun w => (z.1, (reverseWord w, w))
  have hf : Function.Injective f := by
    intro a b h
    simp only [f, Prod.mk.injEq] at h
    exact h.2.2
  rw [Matrix.mul_apply]
  simp_rw [CL_apply]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f))]
  · rw [Finset.sum_image (fun a _ b _ h => hf h)]
    trans ∑ w : Fin k → Fin d, ((if x.2.1 = reverseWord x.2.2 then (1 : ℂ) else 0) *
          (if z.2.1 = reverseWord z.2.2 then 1 else 0)) *
            X (x.1, reverseWord w) (z.1, reverseWord w)
    · refine Finset.sum_congr rfl fun w _ => ?_
      simp only [f, pairedContraction, Matrix.of_apply]
      by_cases h : z.2.1 = reverseWord z.2.2 <;> simp [h] <;> ring
    · rw [← Finset.mul_sum]
      congr 1
      unfold QAlgorithms.traceRight
      rw [Matrix.of_apply]
      exact Equiv.sum_comp (Function.Involutive.toPerm reverseWord rev_rev)
        (fun h => X (x.1, h) (z.1, h))
  · intro y' _ hy'
    have hc : ¬ (y'.1 = z.1 ∧ y'.2.1 = reverseWord y'.2.2 ∧ z.2.1 = reverseWord z.2.2) := by
      rintro ⟨a, b, _⟩
      apply hy'
      refine Finset.mem_image.mpr ⟨y'.2.2, Finset.mem_univ _, ?_⟩
      simp only [f]
      exact Prod.ext a.symm (Prod.ext b.symm rfl)
    simp only [pairedContraction, Matrix.of_apply, if_neg hc, mul_zero]

theorem rhs_apply (d r k : ℕ)
    (X : Matrix ((Fin r → Fin d) × (Fin k → Fin d)) ((Fin r → Fin d) × (Fin k → Fin d)) ℂ)
    (x z : ContractionIndex d r k) :
    (liftSurvivor (k := k) (QAlgorithms.traceRight X) * pairedContraction d r k) x z =
      (if x.2.1 = reverseWord x.2.2 then 1 else 0) *
        (if z.2.1 = reverseWord z.2.2 then 1 else 0) * QAlgorithms.traceRight X x.1 z.1 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (z.1, x.2)]
  · simp only [liftSurvivor, pairedContraction, Matrix.of_apply]
    by_cases h1 : x.2.1 = reverseWord x.2.2 <;> by_cases h2 : z.2.1 = reverseWord z.2.2 <;>
      simp [h1, h2]
  · intro y _ hy
    simp only [liftSurvivor, pairedContraction, Matrix.of_apply]
    by_cases h2 : x.2 = y.2
    · have hc : ¬ (y.1 = z.1 ∧ y.2.1 = reverseWord y.2.2 ∧ z.2.1 = reverseWord z.2.2) := by
        rintro ⟨a, _, _⟩
        exact hy (Prod.ext a h2.symm)
      rw [if_neg hc, mul_zero]
    · rw [if_neg h2]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

end Aux_P18cs

open QAlgorithms.Papers.Independent.Extend50.P18 in
theorem solution (d r k : ℕ) (hd : 0 < d) (hk : 0 < k)
    (X : Matrix ((Fin r → Fin d) × (Fin k → Fin d)) ((Fin r → Fin d) × (Fin k → Fin d)) ℂ) :
    pairedContraction d r k * liftInput X * pairedContraction d r k =
      liftSurvivor (k := k) (QAlgorithms.traceRight X) * pairedContraction d r k := by
  ext x z
  rw [Aux_P18cs.lhs_apply, Aux_P18cs.rhs_apply]

end
