-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.finite_singularities_of_irreducible_bound
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:52:15.854873+00:00
-- url     : https://prove2.me/submissions/d6c60bf5-7ec7-4149-9ad3-488f64c85224

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_card_normalizedFactors_le_totalDegree
import Theorems.Thm_PachDeZeeuw_Algebraic_factor_intersection_bound
import Theorems.Thm_PachDeZeeuw_Algebraic_totalDegree_pderiv_le
import Theorems.Thm_PachDeZeeuw_Algebraic_totalDegree_pderiv_le_sub_one
import Theorems.Thm_PachDeZeeuw_Algebraic_zeroSet_subset_normalizedFactor_union

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve
namespace PachDeZeeuw.Algebraic

/-- A nonzero partial derivative of a positive-degree plane polynomial has strictly smaller
degree. -/
lemma totalDegree_pderiv_lt_of_nonzero
    (h : MvPolynomial (Fin 2) ℝ) {i : Fin 2}
    (hpos : 0 < h.totalDegree)
    (_hpi : MvPolynomial.pderiv i h ≠ 0) :
    (MvPolynomial.pderiv i h).totalDegree < h.totalDegree := by
  have hle := totalDegree_pderiv_le_sub_one h i hpos
  omega

/-- An irreducible plane polynomial does not divide a nonzero partial derivative of itself. -/
lemma irreducible_not_dvd_nonzero_partial
    (h : PlanePoly) (hh : Irreducible h) {i : Fin 2}
    (hpi : MvPolynomial.pderiv i h ≠ 0) :
    ¬ h ∣ MvPolynomial.pderiv i h := by
  intro hdiv
  have hpos : 0 < h.totalDegree := by
    by_contra hnonpos
    have hdeg0 : h.totalDegree = 0 := by omega
    have hC : h = MvPolynomial.C (MvPolynomial.coeff 0 h) := by
      exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hdeg0
    have hcoeff : MvPolynomial.coeff 0 h ≠ 0 := by
      intro hzero
      exact hh.ne_zero (by rw [hC, hzero]; simp)
    have hunit : IsUnit h := by
      rw [hC]
      exact IsUnit.map (MvPolynomial.C : ℝ →+* MvPolynomial (Fin 2) ℝ)
        (isUnit_iff_ne_zero.mpr hcoeff)
    exact hh.not_isUnit hunit
  have hlt := totalDegree_pderiv_lt_of_nonzero h hpos hpi
  have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hpi
  exact (not_lt_of_ge hle) hlt

/-- A normalized factor of the chosen partial derivative cannot be associated with the irreducible
curve. -/
lemma partial_factor_not_associated
    (h k : PlanePoly) (hh : Irreducible h) {i : Fin 2}
    (hpi : MvPolynomial.pderiv i h ≠ 0)
    (hk : k ∈ UniqueFactorizationMonoid.normalizedFactors
        (MvPolynomial.pderiv i h)) :
    ¬ Associated h k := by
  intro hassoc
  have hdiv : h ∣ MvPolynomial.pderiv i h := by
    exact (Associated.dvd_iff_dvd_left hassoc).2
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hk)
  exact irreducible_not_dvd_nonzero_partial h hh hpi hdiv

/-- A singular point lies in the zero set of some normalized factor of the chosen partial
derivative. -/
lemma singularPointSet_subset_partial_factor_union
    (h : PlanePoly) {i : Fin 2}
    (hpi : MvPolynomial.pderiv i h ≠ 0) :
    SingularPointSet h ⊆
      ⋃ k ∈ (UniqueFactorizationMonoid.normalizedFactors
          (MvPolynomial.pderiv i h)).toFinset,
        PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k := by
  classical
  intro z hz
  rw [SingularPointSet, Set.mem_inter_iff, Set.mem_inter_iff] at hz
  obtain ⟨⟨hz0, hz1⟩, hz2⟩ := hz
  fin_cases i
  · have hsubset := zeroSet_subset_normalizedFactor_union
        (p := MvPolynomial.pderiv (0 : Fin 2) h) hpi
    have hzder : z ∈ PlaneCurveZeroSet (MvPolynomial.pderiv (0 : Fin 2) h) := by
      simpa [PlaneCurveZeroSet] using hz1
    rcases Set.mem_iUnion.mp (hsubset hzder) with ⟨k, hk⟩
    rcases Set.mem_iUnion.mp hk with ⟨hkmem, hzk⟩
    refine Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hkmem, ?_⟩⟩
    exact ⟨hz0, hzk⟩
  · have hsubset := zeroSet_subset_normalizedFactor_union
        (p := MvPolynomial.pderiv (1 : Fin 2) h) hpi
    have hzder : z ∈ PlaneCurveZeroSet (MvPolynomial.pderiv (1 : Fin 2) h) := by
      simpa [PlaneCurveZeroSet] using hz2
    rcases Set.mem_iUnion.mp (hsubset hzder) with ⟨k, hk⟩
    rcases Set.mem_iUnion.mp hk with ⟨hkmem, hzk⟩
    refine Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hkmem, ?_⟩⟩
    exact ⟨hz0, hzk⟩

end PachDeZeeuw.Algebraic

open PachDeZeeuw.Algebraic in
theorem solution {d : ℕ} (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    {i : Fin 2}
    (hpi : MvPolynomial.pderiv i h ≠ 0) :
    (SingularPointSet h).Finite ∧
      (SingularPointSet h).ncard ≤ (d + 1) ^ 5 := by
  classical
  let s : Multiset (MvPolynomial (Fin 2) ℝ) :=
    UniqueFactorizationMonoid.normalizedFactors (MvPolynomial.pderiv i h)
  have hsubset :
      SingularPointSet h ⊆
        ⋃ k ∈ s.toFinset, PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k := by
    simpa [s] using singularPointSet_subset_partial_factor_union h hpi
  have hfactor_bound : ∀ k ∈ s.toFinset,
      (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
        (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ (d + 1) ^ 4 := by
    intro k hk
    have hk' : k ∈ s := by
      exact Multiset.mem_toFinset.mp hk
    exact factor_intersection_bound h hh hdeg hpi hk'
      (partial_factor_not_associated h k hh hpi hk')
  have hfinite_union :
      (⋃ k ∈ s.toFinset, PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite := by
    exact Set.Finite.biUnion s.toFinset.finite_toSet (by
      intro k hk
      exact (hfactor_bound k hk).1)
  have hcard_union :
      (SingularPointSet h).ncard ≤
        (⋃ k ∈ s.toFinset, PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard := by
    exact Set.ncard_le_ncard hsubset hfinite_union
  have hcard_biUnion :
      (⋃ k ∈ s.toFinset, PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤
        ∑ k ∈ s.toFinset, (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard := by
    simpa using
      Finset.set_ncard_biUnion_le s.toFinset
        (fun k => PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k)
  have hsum :
      ∑ k ∈ s.toFinset, (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤
        s.toFinset.card * (d + 1) ^ 4 := by
    have hsum' :
        ∑ k ∈ s.toFinset, (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤
          ∑ k ∈ s.toFinset, (d + 1) ^ 4 := by
      refine Finset.sum_le_sum ?_
      intro k hk
      exact (hfactor_bound k hk).2
    calc
      ∑ k ∈ s.toFinset, (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤
          ∑ k ∈ s.toFinset, (d + 1) ^ 4 := hsum'
      _ = s.toFinset.card * (d + 1) ^ 4 := by simp
  have hcard_s : s.toFinset.card ≤ d := by
    calc
      s.toFinset.card ≤ s.card := Multiset.toFinset_card_le _
      _ ≤ (MvPolynomial.pderiv i h).totalDegree :=
        card_normalizedFactors_le_totalDegree (p := MvPolynomial.pderiv i h) hpi
      _ ≤ h.totalDegree := totalDegree_pderiv_le h i
      _ ≤ d := hdeg
  have hcard_mul :
      s.toFinset.card * (d + 1) ^ 4 ≤ d * (d + 1) ^ 4 := by
    exact Nat.mul_le_mul_right _ hcard_s
  have hpow : d * (d + 1) ^ 4 ≤ (d + 1) ^ 5 := by
    calc
      d * (d + 1) ^ 4 ≤ (d + 1) * (d + 1) ^ 4 := by
        exact Nat.mul_le_mul_right _ (Nat.le_succ d)
      _ = (d + 1) ^ 5 := by
        ring_nf
  have hfinite : (SingularPointSet h).Finite := hfinite_union.subset hsubset
  exact ⟨hfinite, le_trans hcard_union (le_trans hcard_biUnion (le_trans hsum (le_trans hcard_mul hpow)))⟩
