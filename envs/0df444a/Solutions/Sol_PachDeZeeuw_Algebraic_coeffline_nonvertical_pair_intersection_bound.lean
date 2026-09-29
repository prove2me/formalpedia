-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.coeffline_nonvertical_pair_intersection_bound
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:47:02.905221+00:00
-- url     : https://prove2.me/submissions/de212d0f-c3e0-4caa-ba06-e9f68f5c938a

import Mathlib
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_coeffLineFactor_dvd_of_specialized_zero
import Theorems.Thm_PachDeZeeuw_Algebraic_eval_eq_specialized_eval
import Theorems.Thm_PachDeZeeuw_Algebraic_finite_coeff_roots_of_ne_zero
import Theorems.Thm_PachDeZeeuw_Algebraic_mem_CoeffLineZeroSet
import Theorems.Thm_PachDeZeeuw_Algebraic_ncard_coeff_roots_le_totalDegree
import Theorems.Thm_PachDeZeeuw_Algebraic_specialized_natDegree_le_totalDegree

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution {d₁ : ℕ} {d₂ : ℕ} (a : XCoeff) (q : MvPolynomial (Fin 2) ℝ)
    (ha0 : a ≠ 0) (_hq0 : q ≠ 0)
    (hadeg : a.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂)
    (_hq0deg : 0 < (Curry0 q).natDegree)
    (hnotDiv :
      ∀ x : ℝ,
        MvPolynomial.eval (fun _ : Fin 1 => x) a = 0 →
          ¬ CoeffLineFactor x ∣ q) :
    (CoeffLineZeroSet a ∩ PlaneCurveZeroSet q).Finite ∧
      (CoeffLineZeroSet a ∩ PlaneCurveZeroSet q).ncard ≤ d₁ * d₂ := by
  classical
  have hrootFinite : (CoeffRootSet a).Finite := finite_coeff_roots_of_ne_zero a ha0
  let rootFinset := hrootFinite.toFinset
  let fiberSet : ℝ → Set Point2 :=
    fun x => {z : Point2 | coeffCoord z = x ∧ z ∈ PlaneCurveZeroSet q}
  have hcover : CoeffLineZeroSet a ∩ PlaneCurveZeroSet q = ⋃ x ∈ rootFinset, fiberSet x := by
    ext z
    constructor
    · intro hz
      have hxroot : coeffCoord z ∈ CoeffRootSet a := by
        simpa [CoeffLineZeroSet, CoeffRootSet, coeffCoord] using hz.1
      have hx : coeffCoord z ∈ rootFinset := by
        simpa [rootFinset] using hxroot
      have hzfiber : z ∈ fiberSet (coeffCoord z) := by
        exact ⟨rfl, hz.2⟩
      refine Set.mem_iUnion.2 ?_
      refine ⟨coeffCoord z, Set.mem_iUnion.2 ?_⟩
      exact ⟨hx, hzfiber⟩
    · intro hz
      rcases Set.mem_iUnion.1 hz with ⟨x, hz⟩
      rcases Set.mem_iUnion.1 hz with ⟨hx, hz⟩
      rcases hz with ⟨hcoeff, hzq⟩
      have hxroot : x ∈ CoeffRootSet a := by
        simpa [rootFinset] using hx
      have hzline : z ∈ CoeffLineZeroSet a := by
        rw [mem_CoeffLineZeroSet]
        change MvPolynomial.eval (fun _ : Fin 1 => coeffCoord z) a = 0
        rw [hcoeff]
        simpa [CoeffRootSet] using hxroot
      exact ⟨hzline, hzq⟩
  have hfiber_finite : ∀ x ∈ rootFinset, (fiberSet x).Finite := by
    intro x hx
    have hxroot : x ∈ CoeffRootSet a := by
      simpa [rootFinset] using hx
    have hqneq : Specialized0 x q ≠ 0 := by
      intro hzero
      exact hnotDiv x hxroot (coeffLineFactor_dvd_of_specialized_zero q x hzero)
    have htarget_finite : ((Specialized0 x q).rootSet ℝ).Finite := by
      have hfinRoots : {y : ℝ | Polynomial.IsRoot (Specialized0 x q) y}.Finite :=
        Polynomial.finite_setOfPred_isRoot hqneq
      have hsubset : (Specialized0 x q).rootSet ℝ ⊆
          {y : ℝ | Polynomial.IsRoot (Specialized0 x q) y} := by
        intro y hy
        rw [Polynomial.mem_rootSet] at hy
        exact hy.2
      exact Set.Finite.subset hfinRoots hsubset
    have hmapsTo : Set.MapsTo elimCoord (fiberSet x) ((Specialized0 x q).rootSet ℝ) := by
      intro z hz
      rcases hz with ⟨hcoeff, hzq⟩
      rw [Polynomial.mem_rootSet]
      constructor
      · exact hqneq
      · have hzspec : Polynomial.eval (elimCoord z) (Specialized0 (coeffCoord z) q) = 0 := by
          rw [← eval_eq_specialized_eval q z]
          exact hzq
        simpa [hcoeff] using hzspec
    have hinj : Set.InjOn elimCoord (fiberSet x) := by
      intro z₁ hz₁ z₂ hz₂ h
      ext i
      fin_cases i
      · exact h
      · exact by
          simpa [coeffCoord] using (hz₁.1.trans hz₂.1.symm)
    exact Set.Finite.of_injOn hmapsTo hinj htarget_finite
  have hfiber_bound : ∀ x ∈ rootFinset, (fiberSet x).ncard ≤ d₂ := by
    intro x hx
    have hxroot : x ∈ CoeffRootSet a := by
      simpa [rootFinset] using hx
    have hqneq : Specialized0 x q ≠ 0 := by
      intro hzero
      exact hnotDiv x hxroot (coeffLineFactor_dvd_of_specialized_zero q x hzero)
    have htarget_finite : ((Specialized0 x q).rootSet ℝ).Finite := by
      have hfinRoots : {y : ℝ | Polynomial.IsRoot (Specialized0 x q) y}.Finite :=
        Polynomial.finite_setOfPred_isRoot hqneq
      have hsubset : (Specialized0 x q).rootSet ℝ ⊆
          {y : ℝ | Polynomial.IsRoot (Specialized0 x q) y} := by
        intro y hy
        rw [Polynomial.mem_rootSet] at hy
        exact hy.2
      exact Set.Finite.subset hfinRoots hsubset
    have hmapsTo : Set.MapsTo elimCoord (fiberSet x) ((Specialized0 x q).rootSet ℝ) := by
      intro z hz
      rcases hz with ⟨hcoeff, hzq⟩
      rw [Polynomial.mem_rootSet]
      constructor
      · exact hqneq
      · have hzspec : Polynomial.eval (elimCoord z) (Specialized0 (coeffCoord z) q) = 0 := by
          rw [← eval_eq_specialized_eval q z]
          exact hzq
        simpa [hcoeff] using hzspec
    have hinj : Set.InjOn elimCoord (fiberSet x) := by
      intro z₁ hz₁ z₂ hz₂ h
      ext i
      fin_cases i
      · exact h
      · exact by
          simpa [coeffCoord] using (hz₁.1.trans hz₂.1.symm)
    have hle_root : (fiberSet x).ncard ≤ ((Specialized0 x q).rootSet ℝ).ncard := by
      have : ((Specialized0 x q).rootSet ℝ).Finite := htarget_finite
      exact Set.ncard_le_ncard_of_injOn elimCoord hmapsTo hinj
    have hroot : ((Specialized0 x q).rootSet ℝ).ncard ≤ (Specialized0 x q).natDegree := by
      simpa using (Polynomial.ncard_rootSet_le (Specialized0 x q) ℝ)
    have hdeg : (Specialized0 x q).natDegree ≤ d₂ := by
      exact le_trans (specialized_natDegree_le_totalDegree q x) hqdeg
    exact le_trans hle_root (le_trans hroot hdeg)
  have hrootcard : rootFinset.card ≤ d₁ := by
    have hrootcard' : rootFinset.card = (CoeffRootSet a).ncard := by
      simpa [rootFinset] using
        (Set.ncard_eq_toFinset_card (CoeffRootSet a) hrootFinite).symm
    calc
      rootFinset.card = (CoeffRootSet a).ncard := hrootcard'
      _ ≤ a.totalDegree := ncard_coeff_roots_le_totalDegree a ha0
      _ ≤ d₁ := hadeg
  have hunion_ncard : (⋃ x ∈ rootFinset, fiberSet x).ncard ≤ d₁ * d₂ := by
    refine le_trans (Finset.set_ncard_biUnion_le rootFinset fiberSet) ?_
    have hsum : ∑ x ∈ rootFinset, (fiberSet x).ncard ≤ ∑ x ∈ rootFinset, d₂ := by
      refine Finset.sum_le_sum ?_
      intro x hx
      exact hfiber_bound x hx
    have hsum' : ∑ x ∈ rootFinset, d₂ = rootFinset.card * d₂ := by
      simp
    calc
      ∑ x ∈ rootFinset, (fiberSet x).ncard ≤ ∑ x ∈ rootFinset, d₂ := hsum
      _ = rootFinset.card * d₂ := hsum'
      _ ≤ d₁ * d₂ := Nat.mul_le_mul_right _ hrootcard
  have hunion_finite : (⋃ x ∈ rootFinset, fiberSet x).Finite := by
    have hfinite :
        (⋃ x ∈ (rootFinset : Set ℝ), fiberSet x).Finite := by
      exact Set.Finite.biUnion rootFinset.finite_toSet (by
        intro x hx
        exact hfiber_finite x (by simpa [rootFinset] using hx))
    simpa only [Finset.mem_coe] using hfinite
  have hfinite : (CoeffLineZeroSet a ∩ PlaneCurveZeroSet q).Finite := by
    rw [hcover]
    exact hunion_finite
  have hncard : (CoeffLineZeroSet a ∩ PlaneCurveZeroSet q).ncard ≤ d₁ * d₂ := by
    calc
      (CoeffLineZeroSet a ∩ PlaneCurveZeroSet q).ncard = (⋃ x ∈ rootFinset, fiberSet x).ncard := by
        rw [hcover]
      _ ≤ d₁ * d₂ := hunion_ncard
  exact ⟨hfinite, hncard⟩
