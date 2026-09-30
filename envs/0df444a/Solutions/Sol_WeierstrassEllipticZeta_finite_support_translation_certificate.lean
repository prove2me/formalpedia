-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_support_translation_certificate
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T03:58:49.717111+00:00
-- url     : https://prove2.me/submissions/d9b3e5da-4028-4f05-9245-cb2e9fd9b426

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Set.Card

open scoped Pointwise

noncomputable section

theorem solution
    (K σ : Type*) [Field K] (p : MvPolynomial σ K) (hp : p ≠ 0)
    (S : Finset (σ →₀ ℕ)) :
    let E : Set (σ →₀ ℕ) := {d | ∀ e ∈ p.support, e + d ∈ S}
    E.Finite ∧ E.ncard ≤ S.card ∧
      ∀ d : σ →₀ ℕ, (p * MvPolynomial.monomial d 1).support ⊆ S ↔ d ∈ E := by
  classical
  let E : Set (σ →₀ ℕ) := {d | ∀ e ∈ p.support, e + d ∈ S}
  obtain ⟨a, ha⟩ := MvPolynomial.support_nonempty.mpr hp
  have hmap : Set.MapsTo (fun d => a + d) E (S : Set (σ →₀ ℕ)) :=
    fun d hd => hd a ha
  have hinj : Set.InjOn (fun d => a + d) E :=
    fun _ _ _ _ h => add_left_cancel h
  have hfinite : E.Finite := Set.Finite.of_injOn hmap hinj S.finite_toSet
  refine ⟨hfinite, ?_, ?_⟩
  · simpa only [Set.ncard_coe_finset] using
      Set.ncard_le_ncard_of_injOn (fun d => a + d) hmap hinj S.finite_toSet
  · intro d
    constructor
    · intro h e he
      apply h
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul_monomial, mul_one]
      exact MvPolynomial.mem_support_iff.mp he
    · intro h i hi
      have hi' : i ∈ p.support + ({d} : Finset (σ →₀ ℕ)) := by
        simpa only [MvPolynomial.support_monomial, one_ne_zero, if_false] using
          MvPolynomial.support_mul p (MvPolynomial.monomial d 1) hi
      obtain ⟨e, he, b, hb, hab⟩ := Finset.mem_add.mp hi'
      have hb' : b = d := Finset.mem_singleton.mp hb
      subst b
      rw [← hab]
      exact h e he
