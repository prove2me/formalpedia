-- Prove2me | solution 1 for ResPCDegreeSize.Main.fact_2_1
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T14:47:36.293127+00:00
-- url     : https://prove2.me/submissions/a828a817-4ae3-4acf-9704-3e367f927b6a

import Mathlib
import Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus
open MvPolynomial
namespace ResPCDegreeSize.Main
theorem derivable_mono {n p : ℕ} {Q : Set (Poly n p)} {D E : ℕ}
    (hDE : D ≤ E) {f : Poly n p} (h : PCDerivable Q D f) :
    PCDerivable Q E f := by
  induction h with
  | ax hf hd => exact .ax hf (hd.trans hDE)
  | zero => exact .zero
  | lin a b _ _ ih1 ih2 => exact .lin a b ih1 ih2
  | mulX i _ hd ih => exact .mulX i ih (hd.trans hDE)

theorem derivable_degree {n p : ℕ} {Q : Set (Poly n p)} {D : ℕ}
    {f : Poly n p} (h : PCDerivable Q D f) : f.totalDegree ≤ D := by
  induction h with
  | ax hf hd => exact hd
  | zero => simp
  | lin a b _ _ ih1 ih2 =>
    apply (totalDegree_add _ _).trans
    apply max_le
    · exact (totalDegree_mul _ _).trans (by simpa using ih1)
    · exact (totalDegree_mul _ _).trans (by simpa using ih2)
  | mulX i _ hd ih => exact hd

theorem derivable_X_mul {n p : ℕ} [Fact p.Prime] {Q : Set (Poly n p)} {D : ℕ}
    {f : Poly n p} (hf : PCDerivable Q D f) (i : Fin n) :
    PCDerivable Q (max D (f.totalDegree + 1)) (f * X i) := by
  rw [mul_comm]
  apply PCDerivable.mulX i (derivable_mono (le_max_left _ _) hf)
  exact (totalDegree_mul _ _).trans (by simp only [totalDegree_X]; omega)

theorem derivable_scalar_mul {n p : ℕ} {Q : Set (Poly n p)} {D : ℕ}
    {f : Poly n p} (hf : PCDerivable Q D f) (c : ZMod p) :
    PCDerivable Q D (C c * f) := by
  have h := PCDerivable.lin c 0 hf PCDerivable.zero
  simpa using h

theorem derivable_X_pow_mul {n p : ℕ} [Fact p.Prime] {Q : Set (Poly n p)} {D : ℕ}
    {f : Poly n p} (hf : PCDerivable Q D f) (i : Fin n) (k : ℕ) :
    PCDerivable Q (max D (f.totalDegree + k)) (f * X i ^ k) := by
  induction k with
  | zero =>
    simpa using derivable_mono (le_max_left D f.totalDegree) hf
  | succ k ih =>
    have hdeg : (f * X i ^ k).totalDegree ≤ f.totalDegree + k :=
      (totalDegree_mul _ _).trans (by simp)
    have hx := derivable_X_mul ih i
    have hbound : max (max D (f.totalDegree + k)) ((f * X i ^ k).totalDegree + 1) ≤
        max D (f.totalDegree + (k+1)) := by
      apply max_le
      · apply max_le
        · exact le_max_left _ _
        · exact (by omega : f.totalDegree + k ≤ f.totalDegree + (k+1)) |>.trans (le_max_right _ _)
      · exact (by omega : (f * X i ^ k).totalDegree + 1 ≤ f.totalDegree + (k+1)) |>.trans (le_max_right _ _)
    have hout := derivable_mono hbound hx
    simpa [pow_succ, mul_assoc] using hout

theorem derivable_prod_X_pow {n p : ℕ} [Fact p.Prime] {Q : Set (Poly n p)} {D : ℕ}
    {f : Poly n p} (hf : PCDerivable Q D f) (s : Finset (Fin n)) (e : Fin n → ℕ) :
    PCDerivable Q (max D (f.totalDegree + ∑ i ∈ s, e i))
      (f * ∏ i ∈ s, (X i : Poly n p) ^ e i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using derivable_mono (le_max_left D f.totalDegree) hf
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi]
    have hdeg : (f * ∏ j ∈ s, (X j : Poly n p) ^ e j).totalDegree ≤
        f.totalDegree + ∑ j ∈ s, e j :=
      (totalDegree_mul _ _).trans (by
        gcongr
        exact (totalDegree_finsetProd s _).trans (by simp))
    have hx := derivable_X_pow_mul ih i (e i)
    have hb : max (max D (f.totalDegree + ∑ j ∈ s, e j))
        ((f * ∏ j ∈ s, (X j : Poly n p) ^ e j).totalDegree + e i) ≤
        max D (f.totalDegree + (e i + ∑ j ∈ s, e j)) := by
      apply max_le
      · apply max_le
        · exact le_max_left _ _
        · exact (by omega : f.totalDegree + ∑ j ∈ s, e j ≤ f.totalDegree + (e i + ∑ j ∈ s, e j)) |>.trans (le_max_right _ _)
      · exact (by omega : (f * ∏ j ∈ s, (X j : Poly n p) ^ e j).totalDegree + e i ≤ f.totalDegree + (e i + ∑ j ∈ s, e j)) |>.trans (le_max_right _ _)
    have hout := derivable_mono hb hx
    simpa [mul_assoc, mul_left_comm, mul_comm] using hout

theorem derivable_monomial_mul {n p : ℕ} [Fact p.Prime] {Q : Set (Poly n p)} {D : ℕ}
    {f : Poly n p} (hf : PCDerivable Q D f) (m : Fin n →₀ ℕ) (c : ZMod p) :
    PCDerivable Q (max D (f.totalDegree + m.sum (fun _ k => k))) (f * monomial m c) := by
  classical
  have h := derivable_prod_X_pow hf m.support (fun i => m i)
  have hc := derivable_scalar_mul h c
  rw [monomial_eq]
  simp only [Finsupp.prod, Finsupp.sum] at hc ⊢
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hc

theorem multiply_bounded {n p : ℕ} [Fact p.Prime] (A : Set (Poly n p)) (D : ℕ)
    (f g : Poly n p) (hf : PCDerivable A D f) :
    PCDerivable A (max D (f.totalDegree + g.totalDegree)) (f * g) := by
  classical
  let bound := max D (f.totalDegree + g.totalDegree)
  have hterm : ∀ m ∈ g.support,
      f * monomial m (coeff m g) ∈ CD A bound := by
    intro m hm
    change PCDerivable A bound (f * monomial m (coeff m g))
    apply derivable_mono _ (derivable_monomial_mul hf m (coeff m g))
    apply max_le_max_left
    exact Nat.add_le_add_left (le_totalDegree hm) _
  have hsum : (∑ m ∈ g.support, f * monomial m (coeff m g)) ∈ CD A bound :=
    Submodule.sum_mem _ hterm
  have heq : f * g = ∑ m ∈ g.support, f * monomial m (coeff m g) := by
    conv_lhs => rw [g.as_sum]
    rw [Finset.mul_sum]
  rw [heq]
  exact hsum

end ResPCDegreeSize.Main
open ResPCDegreeSize.Main

theorem solution {n p : ℕ} [Fact p.Prime] (A : Set (Poly n p)) (D : ℕ) :
    (∀ f g : Poly n p, PCDerivable A D f →
      PCDerivable A (max D (f.totalDegree + g.totalDegree)) (f * g)) ∧
    (∀ f g : Poly n p, f ∈ CD A D → f.totalDegree + g.totalDegree ≤ D → f * g ∈ CD A D) := by
  constructor
  · exact fun f g hf => ResPCDegreeSize.Main.multiply_bounded A D f g hf
  · intro f g hf hdeg
    change PCDerivable A D (f * g)
    have h := ResPCDegreeSize.Main.multiply_bounded A D f g hf
    rwa [max_eq_left hdeg] at h

#print axioms solution
