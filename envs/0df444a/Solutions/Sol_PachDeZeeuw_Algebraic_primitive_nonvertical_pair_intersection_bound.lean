-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.primitive_nonvertical_pair_intersection_bound
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:47:04.721949+00:00
-- url     : https://prove2.me/submissions/273cf6c6-35e5-438b-b547-c787d20d25ad

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_coeffEval_eq_eval_XCoeffEquiv
import Theorems.Thm_PachDeZeeuw_Algebraic_degreeOf_resultant_le
import Theorems.Thm_PachDeZeeuw_Algebraic_eval_eq_specialized_eval
import Theorems.Thm_PachDeZeeuw_Algebraic_fiber_ncard_le_max_totalDegree
import Theorems.Thm_PachDeZeeuw_Algebraic_finite_coeff_roots_of_ne_zero
import Theorems.Thm_PachDeZeeuw_Algebraic_mem_PlaneCurveZeroSet
import Theorems.Thm_PachDeZeeuw_Algebraic_not_both_specializations_zero_of_isRelPrime
import Theorems.Thm_PachDeZeeuw_Algebraic_resultant_ne_zero_of_isRelPrime_primitive_curry

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve
namespace PachDeZeeuw.Algebraic

/-- A nonzero specialization has finitely many common fibers. -/
lemma fiber_finite_of_one_specialization_nonzero
    (p q : MvPolynomial (Fin 2) ℝ) (x : ℝ)
    (h : Specialized0 x p ≠ 0 ∨ Specialized0 x q ≠ 0) :
    (FiberCommonZeros x p q).Finite := by
  rcases h with hp | hq
  · refine Set.Finite.subset (Polynomial.finite_setOfPred_isRoot hp) ?_
    intro y hy
    exact hy.1
  · refine Set.Finite.subset (Polynomial.finite_setOfPred_isRoot hq) ?_
    intro y hy
    exact hy.2

/-- The real root set of a nonzero coefficient polynomial is bounded by its `degreeOf`. -/
lemma ncard_coeff_roots_le_degreeOf
    (r : XCoeff) (hr : r ≠ 0) :
    (CoeffRootSet r).ncard ≤ MvPolynomial.degreeOf (0 : Fin 1) r := by
  have hr' : XCoeffEquiv r ≠ 0 := by
    intro h0
    have h0' : XCoeffEquiv r = XCoeffEquiv 0 := by
      simpa using h0
    exact hr (XCoeffEquiv.injective h0')
  have hrootset_eq :
      CoeffRootSet r = (XCoeffEquiv r).rootSet ℝ := by
    ext x
    rw [Polynomial.mem_rootSet]
    constructor
    · intro hx
      refine ⟨hr', ?_⟩
      change coeffEval x r = 0 at hx
      change Polynomial.eval x (XCoeffEquiv r) = 0
      rw [coeffEval_eq_eval_XCoeffEquiv]
      exact hx
    · intro hx
      change coeffEval x r = 0
      rw [← coeffEval_eq_eval_XCoeffEquiv]
      simpa only [Polynomial.coe_aeval_eq_eval] using hx.2
  have hroot :
      (CoeffRootSet r).ncard ≤ (XCoeffEquiv r).natDegree := by
    simpa [hrootset_eq] using (Polynomial.ncard_rootSet_le (XCoeffEquiv r) ℝ)
  have hdeg : (XCoeffEquiv r).natDegree = MvPolynomial.degreeOf (0 : Fin 1) r := by
    calc
      (XCoeffEquiv r).natDegree = ((MvPolynomial.finSuccEquiv ℝ 0) r).natDegree := by
        simpa [XCoeffEquiv] using
          (Polynomial.natDegree_map_eq_of_injective
            (f := (MvPolynomial.isEmptyAlgEquiv ℝ (Fin 0)).toRingEquiv.toRingHom)
            ((MvPolynomial.isEmptyAlgEquiv ℝ (Fin 0)).toRingEquiv.injective)
            ((MvPolynomial.finSuccEquiv ℝ 0) r))
      _ = MvPolynomial.degreeOf (0 : Fin 1) r := by
        simpa using (MvPolynomial.natDegree_finSuccEquiv (R := ℝ) (n := 0) r)
  simpa [hdeg] using hroot

/-- A common zero gives a root of the coefficient resultant. -/
lemma resultant_vanishes_at_common_zero
    (p q : MvPolynomial (Fin 2) ℝ) {z : Point2}
    (hp0deg : 0 < (Curry0 p).natDegree)
    (_hq0deg : 0 < (Curry0 q).natDegree)
    (hz : z ∈ PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q) :
    coeffCoord z ∈ CoeffRootSet (ResultantCoeff p q) := by
  rw [CoeffRootSet]
  have hp : Polynomial.eval (elimCoord z) (Specialized0 (coeffCoord z) p) = 0 := by
    rw [← eval_eq_specialized_eval]
    exact hz.1
  have hq : Polynomial.eval (elimCoord z) (Specialized0 (coeffCoord z) q) = 0 := by
    rw [← eval_eq_specialized_eval]
    exact hz.2
  have hm : (Specialized0 (coeffCoord z) p).natDegree ≤ (Curry0 p).natDegree := by
    simpa [Specialized0] using
      (Polynomial.natDegree_map_le (f := coeffEval (coeffCoord z)) (p := Curry0 p))
  have hn : (Specialized0 (coeffCoord z) q).natDegree ≤ (Curry0 q).natDegree := by
    simpa [Specialized0] using
      (Polynomial.natDegree_map_le (f := coeffEval (coeffCoord z)) (p := Curry0 q))
  have hbez :
      ∃ u v,
        u.degree < ↑(Curry0 q).natDegree ∧
        v.degree < ↑(Curry0 p).natDegree ∧
        Specialized0 (coeffCoord z) p * u + Specialized0 (coeffCoord z) q * v =
          Polynomial.C
            (Polynomial.resultant (Specialized0 (coeffCoord z) p)
              (Specialized0 (coeffCoord z) q)
              (Curry0 p).natDegree (Curry0 q).natDegree) := by
    exact Polynomial.exists_mul_add_mul_eq_C_resultant
      (f := Specialized0 (coeffCoord z) p) (g := Specialized0 (coeffCoord z) q)
      hm hn (Or.inl (Nat.ne_of_gt hp0deg))
  rcases hbez with ⟨u, v, hu, hv, hbez⟩
  have hzero :
      Polynomial.eval (elimCoord z)
        (Polynomial.C
          (Polynomial.resultant (Specialized0 (coeffCoord z) p)
            (Specialized0 (coeffCoord z) q)
            (Curry0 p).natDegree (Curry0 q).natDegree)) = 0 := by
    rw [← hbez]
    simp [hp, hq]
  simpa [ResultantCoeff, Specialized0, coeffEval] using hzero

end PachDeZeeuw.Algebraic

open PachDeZeeuw.Algebraic in
theorem solution (p q : MvPolynomial (Fin 2) ℝ)
    {d₁ d₂ : ℕ}
    (hpdeg : p.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂)
    (hpprim : (Curry0 p).IsPrimitive)
    (hqprim : (Curry0 q).IsPrimitive)
    (hp0deg : 0 < (Curry0 p).natDegree)
    (hq0deg : 0 < (Curry0 q).natDegree)
    (hrel : IsRelPrime (Curry0 p) (Curry0 q)) :
    (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).Finite ∧
      (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).ncard ≤
        ((d₁ + d₂) ^ 2 + 1) * max d₁ d₂ := by
  classical
  let S : Set Point2 := PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q
  let rootSet : Set ℝ := CoeffRootSet (ResultantCoeff p q)
  have hR : ResultantCoeff p q ≠ 0 := by
    have hp0 : p ≠ 0 := by
      intro hp0
      have hp0' : (Curry0 p).natDegree = 0 := by
        simp [hp0, Curry0]
      rw [hp0'] at hp0deg
      exact (Nat.lt_irrefl 0) hp0deg
    have hq0 : q ≠ 0 := by
      intro hq0
      have hq0' : (Curry0 q).natDegree = 0 := by
        simp [hq0, Curry0]
      rw [hq0'] at hq0deg
      exact (Nat.lt_irrefl 0) hq0deg
    simpa [ResultantCoeff] using
      (resultant_ne_zero_of_isRelPrime_primitive_curry p q hpprim hqprim hrel)
  have hrootFinite : rootSet.Finite := by
    simpa [rootSet] using (finite_coeff_roots_of_ne_zero (ResultantCoeff p q) hR)
  let rootFinset := hrootFinite.toFinset
  let fiberSet : ℝ → Set Point2 :=
    fun x => {z : Point2 | coeffCoord z = x ∧ z ∈ S}
  have hroot_ncard : rootSet.ncard ≤ (d₁ + d₂) ^ 2 := by
    exact le_trans (ncard_coeff_roots_le_degreeOf (ResultantCoeff p q) hR)
      (degreeOf_resultant_le p q hpdeg hqdeg)
  have hfiber_finite : ∀ x ∈ rootFinset, (fiberSet x).Finite := by
    intro x hx
    have hxroot : x ∈ rootSet := by
      simpa [rootFinset, rootSet] using hx
    have hnonzero : Specialized0 x p ≠ 0 ∨ Specialized0 x q ≠ 0 := by
      exact not_both_specializations_zero_of_isRelPrime p q x hpprim hqprim hrel
    have htarget_finite : (FiberCommonZeros x p q).Finite := by
      exact fiber_finite_of_one_specialization_nonzero p q x hnonzero
    have hmapsTo : Set.MapsTo elimCoord (fiberSet x) (FiberCommonZeros x p q) := by
      intro z hz
      rcases hz with ⟨hcoeff, hz⟩
      rcases hz with ⟨hzp, hzq⟩
      constructor
      · simpa [FiberCommonZeros, hcoeff, eval_eq_specialized_eval] using hzp
      · simpa [FiberCommonZeros, hcoeff, eval_eq_specialized_eval] using hzq
    have hinj : Set.InjOn elimCoord (fiberSet x) := by
      intro z₁ hz₁ z₂ hz₂ h
      ext i
      fin_cases i
      · exact h
      · exact by
          simpa [coeffCoord] using (hz₁.1.trans hz₂.1.symm)
    exact Set.Finite.of_injOn hmapsTo hinj htarget_finite
  have hfiber_bound : ∀ x ∈ rootFinset, (fiberSet x).ncard ≤ max d₁ d₂ := by
    intro x hx
    have hxroot : x ∈ rootSet := by
      simpa [rootFinset, rootSet] using hx
    have hnonzero : Specialized0 x p ≠ 0 ∨ Specialized0 x q ≠ 0 := by
      exact not_both_specializations_zero_of_isRelPrime p q x hpprim hqprim hrel
    have hle_root : (fiberSet x).ncard ≤ (FiberCommonZeros x p q).ncard := by
      have htarget_finite : (FiberCommonZeros x p q).Finite := by
        exact fiber_finite_of_one_specialization_nonzero p q x hnonzero
      have hmapsTo : Set.MapsTo elimCoord (fiberSet x) (FiberCommonZeros x p q) := by
        intro z hz
        rcases hz with ⟨hcoeff, hz⟩
        rcases hz with ⟨hzp, hzq⟩
        constructor
        · simpa [FiberCommonZeros, hcoeff, eval_eq_specialized_eval] using hzp
        · simpa [FiberCommonZeros, hcoeff, eval_eq_specialized_eval] using hzq
      have hinj : Set.InjOn elimCoord (fiberSet x) := by
        intro z₁ hz₁ z₂ hz₂ h
        ext i
        fin_cases i
        · exact h
        · exact by
            simpa [coeffCoord] using (hz₁.1.trans hz₂.1.symm)
      exact Set.ncard_le_ncard_of_injOn elimCoord hmapsTo hinj htarget_finite
    have hfiberBound : (FiberCommonZeros x p q).ncard ≤ max d₁ d₂ := by
      exact le_trans (fiber_ncard_le_max_totalDegree p q x hnonzero) (max_le_max hpdeg hqdeg)
    exact le_trans hle_root hfiberBound
  have hcover : S = ⋃ x ∈ rootFinset, fiberSet x := by
    ext z
    constructor
    · intro hz
      have hxroot : coeffCoord z ∈ rootSet := by
        exact resultant_vanishes_at_common_zero p q hp0deg hq0deg hz
      have hx : coeffCoord z ∈ rootFinset := by
        simpa [rootFinset, rootSet] using hxroot
      have hzfiber : z ∈ fiberSet (coeffCoord z) := by
        exact ⟨rfl, hz⟩
      refine Set.mem_iUnion.2 ?_
      refine ⟨coeffCoord z, Set.mem_iUnion.2 ?_⟩
      exact ⟨hx, hzfiber⟩
    · intro hz
      rcases Set.mem_iUnion.1 hz with ⟨x, hz⟩
      rcases Set.mem_iUnion.1 hz with ⟨hx, hz⟩
      rcases hz with ⟨hcoeff, hzS⟩
      simpa [S] using hzS
  have hrootcard : rootFinset.card ≤ (d₁ + d₂) ^ 2 + 1 := by
    have hrootcard' : rootFinset.card = rootSet.ncard := by
      simpa [rootFinset, rootSet] using
        (Set.ncard_eq_toFinset_card rootSet hrootFinite).symm
    calc
      rootFinset.card = rootSet.ncard := hrootcard'
      _ ≤ (d₁ + d₂) ^ 2 := hroot_ncard
      _ ≤ (d₁ + d₂) ^ 2 + 1 := Nat.le_succ _
  have hunion_ncard :
      (⋃ x ∈ rootFinset, fiberSet x).ncard ≤ ((d₁ + d₂) ^ 2 + 1) * max d₁ d₂ := by
    refine le_trans (Finset.set_ncard_biUnion_le rootFinset fiberSet) ?_
    have hsum :
        ∑ x ∈ rootFinset, (fiberSet x).ncard ≤ ∑ x ∈ rootFinset, max d₁ d₂ := by
      refine Finset.sum_le_sum ?_
      intro x hx
      exact hfiber_bound x hx
    have hsum' : ∑ x ∈ rootFinset, max d₁ d₂ = rootFinset.card * max d₁ d₂ := by
      simp
    calc
      ∑ x ∈ rootFinset, (fiberSet x).ncard ≤ ∑ x ∈ rootFinset, max d₁ d₂ := hsum
      _ = rootFinset.card * max d₁ d₂ := hsum'
      _ ≤ ((d₁ + d₂) ^ 2 + 1) * max d₁ d₂ := by
        exact Nat.mul_le_mul_right _ hrootcard
  have hunion_finite : (⋃ x ∈ rootFinset, fiberSet x).Finite := by
    change (⋃ x ∈ (rootFinset : Set ℝ), fiberSet x).Finite
    exact Set.Finite.biUnion rootFinset.finite_toSet (by
      intro x hx
      exact hfiber_finite x hx)
  have hfinite : S.Finite := by
    simpa [hcover] using hunion_finite
  have hncard : S.ncard ≤ ((d₁ + d₂) ^ 2 + 1) * max d₁ d₂ := by
    calc
      S.ncard = (⋃ x ∈ rootFinset, fiberSet x).ncard := by rw [hcover]
      _ ≤ ((d₁ + d₂) ^ 2 + 1) * max d₁ d₂ := hunion_ncard
  exact ⟨hfinite, hncard⟩
