-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.card_normalizedFactors_le_totalDegree
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:43:50.815705+00:00
-- url     : https://prove2.me/submissions/b398365c-2ce7-436c-a193-ffde4f5e56c3

import Mathlib
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_normalized_factor_irreducible

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve
namespace PachDeZeeuw.Algebraic

/-- A normalized factor multiset has total degree equal to the total degree of its product. -/
lemma helper_multiset_prod_totalDegree_eq_sum
    (s : Multiset (MvPolynomial (Fin 2) ℝ))
    (hs : ∀ h ∈ s, h ≠ 0) :
    s.prod.totalDegree = (s.map MvPolynomial.totalDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ha : a ≠ 0 := hs a (by simp)
      have hs' : ∀ h ∈ s, h ≠ 0 := by
        intro h hh
        exact hs h (by simp [hh])
      have hs0 : (0 : MvPolynomial (Fin 2) ℝ) ∉ s := by
        intro h0
        exact (hs' 0 h0) rfl
      have ih' := ih hs'
      rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
      rw [MvPolynomial.totalDegree_mul_of_isDomain ha (Multiset.prod_ne_zero hs0)]
      rw [ih']

/-- Normalized factors of a nonzero plane polynomial have positive total degree. -/
lemma normalized_factor_totalDegree_pos
    {p h : MvPolynomial (Fin 2) ℝ}
    (hh : h ∈ UniqueFactorizationMonoid.normalizedFactors p) :
    0 < h.totalDegree := by
  have hirr : Irreducible h := normalized_factor_irreducible hh
  by_contra hpos
  have hdeg0 : h.totalDegree = 0 := by omega
  have hEq : h = MvPolynomial.C (MvPolynomial.coeff 0 h) := by
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hdeg0
  have hcoeff0 : MvPolynomial.coeff 0 h ≠ 0 := by
    intro hzero
    exact hirr.ne_zero (by rw [hEq, hzero]; simp)
  have hunit : IsUnit h := by
    rw [hEq]
    exact IsUnit.map (MvPolynomial.C : ℝ →+* MvPolynomial (Fin 2) ℝ)
      (isUnit_iff_ne_zero.mpr hcoeff0)
  exact hirr.not_isUnit hunit

/-- Associated plane polynomials have the same total degree. -/
lemma totalDegree_eq_of_associated
    {p q : MvPolynomial (Fin 2) ℝ} (h : Associated p q) :
    p.totalDegree = q.totalDegree := by
  by_cases hp0 : p = 0
  · have hq0 : q = 0 := by
      by_contra hq0
      have hpnonzero : p ≠ 0 := (h.ne_zero_iff).2 hq0
      exact hpnonzero hp0
    subst hp0
    subst hq0
    simp
  · have hq0 : q ≠ 0 := (h.ne_zero_iff).1 hp0
    have hpq : p ∣ q := (h.dvd_iff_dvd_right).mp dvd_rfl
    have hqp : q ∣ p := (h.dvd_iff_dvd_left).mp dvd_rfl
    exact le_antisymm
      (MvPolynomial.totalDegree_le_of_dvd_of_isDomain hpq hq0)
      (MvPolynomial.totalDegree_le_of_dvd_of_isDomain hqp hp0)

/-- A small helper for the normalized-factor cardinality bound. -/
lemma helper_card_le_sum_of_pos
    (s : Multiset (MvPolynomial (Fin 2) ℝ))
    (hs : ∀ h ∈ s, 0 < h.totalDegree) :
    s.card ≤ (s.map MvPolynomial.totalDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ha : 0 < a.totalDegree := hs a (by simp)
      have hs' : ∀ h ∈ s, 0 < h.totalDegree := by
        intro h hh
        exact hs h (by simp [hh])
      have ih' := ih hs'
      simp [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons] at ih' ⊢
      omega

end PachDeZeeuw.Algebraic

open PachDeZeeuw.Algebraic in
theorem solution {p : MvPolynomial (Fin 2) ℝ} (hp0 : p ≠ 0) :
    (UniqueFactorizationMonoid.normalizedFactors p).card ≤ p.totalDegree := by
  let s : Multiset (MvPolynomial (Fin 2) ℝ) := UniqueFactorizationMonoid.normalizedFactors p
  have hspos : ∀ h ∈ s, 0 < h.totalDegree := by
    intro h hh
    simpa [s] using (normalized_factor_totalDegree_pos (p := p) (h := h) hh)
  have hscard : s.card ≤ (s.map MvPolynomial.totalDegree).sum :=
    helper_card_le_sum_of_pos s hspos
  have hsnonzero : ∀ h ∈ s, h ≠ 0 := by
    intro h hh
    exact (normalized_factor_irreducible (p := p) (h := h) hh).ne_zero
  have hprod : s.prod.totalDegree = (s.map MvPolynomial.totalDegree).sum :=
    helper_multiset_prod_totalDegree_eq_sum s hsnonzero
  have hassoc : Associated s.prod p := by
    simpa [s] using (UniqueFactorizationMonoid.prod_normalizedFactors hp0)
  have hdeg : s.prod.totalDegree = p.totalDegree := totalDegree_eq_of_associated hassoc
  calc
    s.card ≤ (s.map MvPolynomial.totalDegree).sum := hscard
    _ = s.prod.totalDegree := hprod.symm
    _ = p.totalDegree := hdeg
