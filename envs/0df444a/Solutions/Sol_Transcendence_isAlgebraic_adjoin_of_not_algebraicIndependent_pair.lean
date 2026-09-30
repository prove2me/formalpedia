-- Prove2me | solution 1 for Transcendence.isAlgebraic_adjoin_of_not_algebraicIndependent_pair
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T08:36:29.732705+00:00
-- url     : https://prove2.me/submissions/c70c3c05-6ae5-4bcb-8cdf-85e346d19d95

import Mathlib

/-!
# Pair dependence: `z` is algebraic over `R[t]`

Let `t` be transcendental over `R`, so that the one-element family `t` is algebraically
independent. Suppose that `z` is transcendental over `R[t]`. Then the family indexed by
`Option Unit` that sends `none` to `z` and `some ()` to `t` is algebraically independent
(`AlgebraicIndependent.option_iff_transcendental`), and `![t, z]` is that family composed with the
injection `![some (), none]`, hence algebraically independent too. This contradicts the hypothesis.
-/

theorem solution {R A : Type*} [CommRing R]
    [CommRing A] [Algebra R A] {t z : A} (ht : Transcendental R t)
    (h : ¬ AlgebraicIndependent R ![t, z]) :
    IsAlgebraic ↥(Algebra.adjoin R ({t} : Set A)) z := by
  by_contra hz
  apply h
  -- `t` alone is algebraically independent
  have hind : AlgebraicIndependent R (fun _ : Unit => t) :=
    (algebraicIndependent_singleton_iff ()).2 ht
  -- `z` is transcendental over `R[t]`, so the family `(t, z)` indexed by `Option Unit` is too
  have htrans : Transcendental ↥(Algebra.adjoin R (Set.range fun _ : Unit => t)) z := by
    rw [Set.range_const]
    exact hz
  have hopt := (hind.option_iff_transcendental z).2 htrans
  -- `![t, z]` is that family along an injection `Fin 2 → Option Unit`
  have he : Function.Injective (![some (), none] : Fin 2 → Option Unit) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  convert hopt.comp _ he using 1
  funext i
  fin_cases i <;> rfl
