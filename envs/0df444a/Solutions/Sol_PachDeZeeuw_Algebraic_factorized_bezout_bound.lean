-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.factorized_bezout_bound
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:52:15.274286+00:00
-- url     : https://prove2.me/submissions/07b63258-d2dc-4c92-9de6-d382fd70da30

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_PlaneCurveZeroSet_subset_of_dvd
import Theorems.Thm_PachDeZeeuw_Algebraic_card_normalizedFactors_le_totalDegree
import Theorems.Thm_PachDeZeeuw_Algebraic_finite_singularities_of_irreducible_bound
import Theorems.Thm_PachDeZeeuw_Algebraic_irreducible_has_nonzero_partial
import Theorems.Thm_PachDeZeeuw_Algebraic_irreducible_pair_intersection_bound
import Theorems.Thm_PachDeZeeuw_Algebraic_nonsingular_point_has_infinite_zeroSet_of_partial0
import Theorems.Thm_PachDeZeeuw_Algebraic_nonsingular_point_has_infinite_zeroSet_of_partial1
import Theorems.Thm_PachDeZeeuw_Algebraic_normalized_factor_degree_le
import Theorems.Thm_PachDeZeeuw_Algebraic_normalized_factor_irreducible
import Theorems.Thm_PachDeZeeuw_Algebraic_zeroSet_subset_normalizedFactor_union

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve
namespace PachDeZeeuw.Algebraic

/-- A nonsingular point has an infinite real zero set. -/
theorem nonsingular_point_has_infinite_zeroSet
    (h : PlanePoly) {z : Point2}
    (hz : z ∈ PlaneCurveZeroSet h)
    (hnonsing :
      MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (0 : Fin 2) h) ≠ 0 ∨
      MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (1 : Fin 2) h) ≠ 0) :
    (PlaneCurveZeroSet h).Infinite := by
  rcases hnonsing with h0 | h1
  · exact nonsingular_point_has_infinite_zeroSet_of_partial0 h hz h0
  · exact nonsingular_point_has_infinite_zeroSet_of_partial1 h hz h1

/-- A finite zero set is contained in the singular points. -/
lemma finite_zeroSet_subset_singularities
    (h : PlanePoly)
    (hfin : (PlaneCurveZeroSet h).Finite) :
    PlaneCurveZeroSet h ⊆ SingularPointSet h := by
  intro z hz
  refine ⟨⟨hz, ?_⟩, ?_⟩
  · by_contra h0
    have hinf := nonsingular_point_has_infinite_zeroSet h hz (by
      left
      simpa using h0)
    exact hfin.not_infinite hinf
  · by_contra h1
    have hinf := nonsingular_point_has_infinite_zeroSet h hz (by
      right
      simpa using h1)
    exact hfin.not_infinite hinf

/-- The real zero set of a non-infinite irreducible plane curve is finite with the same bound. -/
theorem finite_real_zero_set_of_irreducible_factor_bound {d : ℕ}
    (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    (hfin : ¬ (PlaneCurveZeroSet h).Infinite) :
    (PlaneCurveZeroSet h).Finite ∧
      (PlaneCurveZeroSet h).ncard ≤ (d + 1) ^ 5 := by
  classical
  have hfinite : (PlaneCurveZeroSet h).Finite := (Set.not_infinite).mp hfin
  have hsubset : PlaneCurveZeroSet h ⊆ SingularPointSet h :=
    finite_zeroSet_subset_singularities h hfinite
  rcases irreducible_has_nonzero_partial h hh with hpi | hpi
  · have hsingu := finite_singularities_of_irreducible_bound h hh hdeg hpi
    exact ⟨hfinite, le_trans (Set.ncard_le_ncard hsubset hsingu.1) hsingu.2⟩
  · have hsingu := finite_singularities_of_irreducible_bound h hh hdeg hpi
    exact ⟨hfinite, le_trans (Set.ncard_le_ncard hsubset hsingu.1) hsingu.2⟩

end PachDeZeeuw.Algebraic

open PachDeZeeuw.Algebraic in
theorem solution {d₁ : ℕ} {d₂ : ℕ} (p q : PlanePoly)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hpdeg : p.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂)
    (hnoinf : ¬ HasCommonInfiniteIrreducibleFactor p q) :
    (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).Finite ∧
      (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).ncard ≤
        (d₁ + d₂ + 1) ^ 8 := by
  classical
  let sp : Multiset (PlanePoly) := UniqueFactorizationMonoid.normalizedFactors p
  let sq : Multiset (PlanePoly) := UniqueFactorizationMonoid.normalizedFactors q
  let pairs : Finset (PlanePoly × PlanePoly) := sp.toFinset.product sq.toFinset
  let pairSet : PlanePoly × PlanePoly → Set Point2 :=
    fun hk => PlaneCurveZeroSet hk.1 ∩ PlaneCurveZeroSet hk.2
  have hcover :
      PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q ⊆ ⋃ x ∈ pairs, pairSet x := by
    intro z hz
    rcases hz with ⟨hzp, hzq⟩
    have hpW := zeroSet_subset_normalizedFactor_union (p := p) hp0 hzp
    have hqW := zeroSet_subset_normalizedFactor_union (p := q) hq0 hzq
    rcases Set.mem_iUnion.mp hpW with ⟨hpFactor, hpW⟩
    rcases Set.mem_iUnion.mp hpW with ⟨hpMem, hzhp⟩
    rcases Set.mem_iUnion.mp hqW with ⟨hqFactor, hqW⟩
    rcases Set.mem_iUnion.mp hqW with ⟨hqMem, hzhq⟩
    refine Set.mem_iUnion.2 ?_
    refine ⟨(hpFactor, hqFactor), Set.mem_iUnion.2 ?_⟩
    refine ⟨by
      exact Finset.mem_product.2 ⟨by
        exact Multiset.mem_toFinset.mpr (Multiset.mem_toFinset.mp hpMem), by
        exact Multiset.mem_toFinset.mpr (Multiset.mem_toFinset.mp hqMem)⟩, ?_⟩
    exact ⟨hzhp, hzhq⟩
  have hpairBound : ∀ x ∈ pairs, (pairSet x).Finite ∧ (pairSet x).ncard ≤ (d₁ + d₂ + 1) ^ 5 := by
    intro x hx
    have hx' : x.1 ∈ sp.toFinset ∧ x.2 ∈ sq.toFinset := by
      simpa [pairs] using hx
    rcases hx' with ⟨hx1, hx2⟩
    have hx1' : x.1 ∈ sp := Multiset.mem_toFinset.mp hx1
    have hx2' : x.2 ∈ sq := Multiset.mem_toFinset.mp hx2
    have hirr : Irreducible x.1 := normalized_factor_irreducible (p := p) (h := x.1) hx1'
    have kirr : Irreducible x.2 := normalized_factor_irreducible (p := q) (h := x.2) hx2'
    have hdeg : x.1.totalDegree ≤ d₁ := by
      exact le_trans
        (normalized_factor_degree_le (p := p) (h := x.1) hp0 hx1')
        hpdeg
    have kdeg : x.2.totalDegree ≤ d₂ := by
      exact le_trans
        (normalized_factor_degree_le (p := q) (h := x.2) hq0 hx2')
        hqdeg
    have hspos : 0 < d₁ + d₂ + 1 := by omega
    by_cases hAssoc : Associated x.1 x.2
    · have hdiv12 : x.1 ∣ x.2 := by
        exact (hAssoc.dvd_iff_dvd_left).2 dvd_rfl
      have hdiv21 : x.2 ∣ x.1 := by
        exact (hAssoc.dvd_iff_dvd_left).1 dvd_rfl
      have hEq : PlaneCurveZeroSet x.1 = PlaneCurveZeroSet x.2 := by
        exact Set.Subset.antisymm
          (PlaneCurveZeroSet_subset_of_dvd hdiv12)
          (PlaneCurveZeroSet_subset_of_dvd hdiv21)
      have hnotinf : ¬ (PlaneCurveZeroSet x.1).Infinite := by
        intro hinf
        have hpdiv : x.1 ∣ p := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hx1'
        have hqdiv : x.1 ∣ q := by
          have hqdiv' : x.2 ∣ q := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hx2'
          exact (hAssoc.dvd_iff_dvd_left).2 hqdiv'
        exact hnoinf ⟨x.1, hirr, hinf, hpdiv, hqdiv⟩
      have hfin := finite_real_zero_set_of_irreducible_factor_bound
        (d := d₁ + d₂) x.1 hirr
        (le_trans hdeg (by omega)) hnotinf
      have hpairFin : (pairSet x).Finite := by
        simpa [pairSet, hEq] using hfin.1
      have hpairNcard : (pairSet x).ncard ≤ (d₁ + d₂ + 1) ^ 5 := by
        simpa [pairSet, hEq] using hfin.2
      exact ⟨hpairFin, hpairNcard⟩
    · have hpair := irreducible_pair_intersection_bound
        (d₁ := d₁) (d₂ := d₂) x.1 x.2 hirr kirr hdeg kdeg hAssoc
      exact ⟨hpair.1, le_trans hpair.2 (Nat.le_mul_of_pos_right _ hspos)⟩
  have hfinitePairs : (⋃ x ∈ pairs, pairSet x).Finite := by
    exact Set.Finite.biUnion pairs.finite_toSet (by
      intro x hx
      exact (hpairBound x hx).1)
  have hcard_cover :
      (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).ncard ≤
        (⋃ x ∈ pairs, pairSet x).ncard := by
    exact Set.ncard_le_ncard hcover hfinitePairs
  have hcard_biUnion :
      (⋃ x ∈ pairs, pairSet x).ncard ≤ ∑ x ∈ pairs, (pairSet x).ncard := by
    simpa [pairSet] using Finset.set_ncard_biUnion_le pairs (fun x => pairSet x)
  have hsum_le :
      ∑ x ∈ pairs, (pairSet x).ncard ≤ pairs.card * (d₁ + d₂ + 1) ^ 5 := by
    calc ∑ x ∈ pairs, (pairSet x).ncard
        ≤ ∑ _x ∈ pairs, (d₁ + d₂ + 1) ^ 5 :=
          Finset.sum_le_sum (fun x hx => (hpairBound x hx).2)
      _ = pairs.card * (d₁ + d₂ + 1) ^ 5 := by
          rw [Finset.sum_const, smul_eq_mul]
  have hpaircard : pairs.card ≤ (d₁ + d₂ + 1) ^ 2 := by
    have hsp : sp.toFinset.card ≤ d₁ := by
      calc
        sp.toFinset.card ≤ sp.card := Multiset.toFinset_card_le _
        _ ≤ p.totalDegree := card_normalizedFactors_le_totalDegree (p := p) hp0
        _ ≤ d₁ := hpdeg
    have hsq : sq.toFinset.card ≤ d₂ := by
      calc
        sq.toFinset.card ≤ sq.card := Multiset.toFinset_card_le _
        _ ≤ q.totalDegree := card_normalizedFactors_le_totalDegree (p := q) hq0
        _ ≤ d₂ := hqdeg
    have hle : sp.toFinset.card * sq.toFinset.card ≤ (d₁ + d₂ + 1) ^ 2 := by
      have hd1 : d₁ ≤ d₁ + d₂ + 1 := by omega
      have hd2 : d₂ ≤ d₁ + d₂ + 1 := by omega
      calc
        sp.toFinset.card * sq.toFinset.card ≤ d₁ * sq.toFinset.card := by
          exact Nat.mul_le_mul_right _ hsp
        _ ≤ d₁ * d₂ := by
          exact Nat.mul_le_mul_left _ hsq
        _ ≤ (d₁ + d₂ + 1) * (d₁ + d₂ + 1) := by
          calc
            d₁ * d₂ ≤ (d₁ + d₂ + 1) * d₂ := Nat.mul_le_mul_right _ hd1
            _ ≤ (d₁ + d₂ + 1) * (d₁ + d₂ + 1) := Nat.mul_le_mul_left _ hd2
        _ = (d₁ + d₂ + 1) ^ 2 := by simp [pow_two]
    simpa [pairs, Finset.card_product] using hle
  have hspos : 0 < d₁ + d₂ + 1 := by omega
  have hfinal :
      pairs.card * (d₁ + d₂ + 1) ^ 5 ≤ (d₁ + d₂ + 1) ^ 8 := by
    calc
      pairs.card * (d₁ + d₂ + 1) ^ 5 ≤ (d₁ + d₂ + 1) ^ 2 * (d₁ + d₂ + 1) ^ 5 := by
        exact Nat.mul_le_mul_right _ hpaircard
      _ = (d₁ + d₂ + 1) ^ 7 := by
        rw [← pow_add]
      _ ≤ (d₁ + d₂ + 1) ^ 8 := by
        exact Nat.le_mul_of_pos_right _ hspos
  have hfinite : (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).Finite := hfinitePairs.subset hcover
  have hcard : (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).ncard ≤
      (d₁ + d₂ + 1) ^ 8 := by
    calc
      (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).ncard ≤
          (⋃ x ∈ pairs, pairSet x).ncard := hcard_cover
      _ ≤ ∑ x ∈ pairs, (pairSet x).ncard := hcard_biUnion
      _ ≤ pairs.card * (d₁ + d₂ + 1) ^ 5 := hsum_le
      _ ≤ (d₁ + d₂ + 1) ^ 8 := hfinal
  exact ⟨hfinite, hcard⟩
