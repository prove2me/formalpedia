-- Prove2me | solution 1 for WeierstrassEllipticZeta.triangular_sparse_bezout_certificate
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T21:06:25.695266+00:00
-- url     : https://prove2.me/submissions/9993c170-4f24-41bd-a1b2-f0c9ed49f886

import Theorems.Thm_WeierstrassEllipticZeta_triangular_prefix_effective_equations
import Theorems.Thm_WeierstrassEllipticZeta_bounded_time_bezout_coefficients
import Mathlib.Data.Fintype.EquivFin

noncomputable section
open scoped Classical

open WeierstrassEllipticZeta

theorem solution
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) (hM : M.Monic)
    (hI : ∀ f : MvPolynomial (Fin 4) ℂ,
      f ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f)
    (p : ℕ → MvPolynomial (Fin 4) ℂ) (n : ℕ)
    (htop : I ⊔ Ideal.span (Set.range (fun i : Fin n => p i.val)) = ⊤) :
    let T := (Finset.range n).filter (fun j =>
      p j ∉ (I ⊔ Ideal.span (Set.range (fun i : Fin j => p i.val))))
    T.card ≤ M.natDegree ∧
    ∃ b : T → Polynomial ℂ,
      (∀ j : T, (b j).degree < (M.natDegree : ℕ) ∧
        (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) (b j)).totalDegree ≤
          M.natDegree - 1) ∧
      1 - ∑ j : T, Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b j) * p j.val ∈ I ∧
      ∀ D : ℕ, (∀ j : T, (p j.val).totalDegree ≤ D) →
        (1 - ∑ j : T, Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b j) * p j.val).totalDegree ≤
          M.natDegree - 1 + D := by
  classical
  let T := (Finset.range n).filter (fun j =>
    p j ∉ (I ⊔ Ideal.span (Set.range (fun i : Fin j => p i.val))))
  have hkeep := triangular_prefix_effective_equations I M r hM hI p n
  have hcard : T.card ≤ M.natDegree := (Nat.le_add_right _ _).trans hkeep.2
  have htop' : I ⊔ Ideal.span (p '' (T : Set ℕ)) = ⊤ := hkeep.1.symm.trans htop
  let e : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  let f : Fin (Fintype.card T) → MvPolynomial (Fin 4) ℂ := fun j => p (e j).val
  have hrange : Set.range f = p '' (T : Set ℕ) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨(e j).val, (e j).property, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨e.symm ⟨j, hj⟩, by simp [f]⟩
  have h1 : (1 : MvPolynomial (Fin 4) ℂ) ∈ I ⊔ Ideal.span (Set.range f) := by
    rw [hrange, htop']
    trivial
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h1
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hv
  have hacert : 1 - ∑ j, a j * f j ∈ I := by
    rw [ha, ← huv, add_sub_cancel_right]
    exact hu
  obtain ⟨b, hb, hcert, hdegree⟩ := bounded_time_bezout_coefficients I M.natDegree M hM
    (Polynomial.degree_eq_natDegree hM.ne_zero) r hI (Fintype.card T) f a hacert
  let b' : T → Polynomial ℂ := fun j => b (e.symm j)
  have hsum : (∑ j : Fin (Fintype.card T),
      Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b j) * f j) =
      ∑ j : T, Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b' j) * p j.val := by
    apply Fintype.sum_equiv e
    intro j
    simp [b', f]
  refine ⟨hcard, b', fun j => ⟨(hb (e.symm j)).1, (hb (e.symm j)).2.1⟩, ?_, ?_⟩
  · rw [← hsum]
    exact hcert
  · intro D hD
    rw [← hsum]
    exact hdegree D (fun j => hD (e j))

