-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.not_both_specializations_zero_of_isRelPrime
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:43:54.122516+00:00
-- url     : https://prove2.me/submissions/0efb6189-1cd4-4c5d-a1b4-09485cf80aec

import Mathlib
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_coeffLineFactor_dvd_of_specialized_zero

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution (p q : MvPolynomial (Fin 2) ℝ) (x : ℝ)
    (_hpprim : (Curry0 p).IsPrimitive)
    (_hqprim : (Curry0 q).IsPrimitive)
    (hrel : IsRelPrime (Curry0 p) (Curry0 q)) :
    Specialized0 x p ≠ 0 ∨ Specialized0 x q ≠ 0 := by
  by_cases hp : Specialized0 x p = 0
  · by_cases hq : Specialized0 x q = 0
    · have hpdvd : CoeffLineFactor x ∣ p :=
        coeffLineFactor_dvd_of_specialized_zero p x hp
      have hqdvd : CoeffLineFactor x ∣ q :=
        coeffLineFactor_dvd_of_specialized_zero q x hq
      have hsymm_p : (MvPolynomial.finSuccEquiv ℝ 1).symm (Curry0 p) = p := by
        rw [Curry0]
        exact (MvPolynomial.finSuccEquiv ℝ 1).symm_apply_apply p
      have hsymm_q : (MvPolynomial.finSuccEquiv ℝ 1).symm (Curry0 q) = q := by
        rw [Curry0]
        exact (MvPolynomial.finSuccEquiv ℝ 1).symm_apply_apply q
      have hpdvd_symm : CoeffLineFactor x ∣ (MvPolynomial.finSuccEquiv ℝ 1).symm (Curry0 p) :=
        by simpa [hsymm_p] using hpdvd
      have hqdvd_symm : CoeffLineFactor x ∣ (MvPolynomial.finSuccEquiv ℝ 1).symm (Curry0 q) :=
        by simpa [hsymm_q] using hqdvd
      have hpdvd' : Curry0 (CoeffLineFactor x) ∣ Curry0 p := by
        exact (map_dvd_iff_dvd_symm (MvPolynomial.finSuccEquiv ℝ 1)).2 hpdvd_symm
      have hqdvd' : Curry0 (CoeffLineFactor x) ∣ Curry0 q := by
        exact (map_dvd_iff_dvd_symm (MvPolynomial.finSuccEquiv ℝ 1)).2 hqdvd_symm
      have hunit0 : IsUnit (Curry0 (CoeffLineFactor x)) := by
        exact (hrel.of_dvd_left hpdvd').isUnit_of_dvd hqdvd'
      have hunit : IsUnit (CoeffLineFactor x) := by
        have hsymm_factor : (MvPolynomial.finSuccEquiv ℝ 1).symm
            (Curry0 (CoeffLineFactor x)) = CoeffLineFactor x := by
          rw [Curry0]
          exact (MvPolynomial.finSuccEquiv ℝ 1).symm_apply_apply (CoeffLineFactor x)
        simpa [hsymm_factor] using
          IsUnit.map (MvPolynomial.finSuccEquiv ℝ 1).symm hunit0
      have hneq : (fun₀ | (1 : Fin 2) => 1) ≠ (0 : (Fin 2 →₀ ℕ)) := by
        intro h
        have := congrArg (fun m => m (1 : Fin 2)) h
        simp at this
      have hcoeff :
          MvPolynomial.coeff (fun₀ | (1 : Fin 2) => 1) (CoeffLineFactor x) = 1 := by
        have hCcoeff :
            MvPolynomial.coeff (fun₀ | (1 : Fin 2) => 1)
              (MvPolynomial.C x) = 0 := by
          rw [MvPolynomial.coeff_C]
          split_ifs with h0
          · exfalso
            exact hneq h0.symm
          · rfl
        rw [CoeffLineFactor, MvPolynomial.coeff_sub]
        simp [hCcoeff]
      have hnil :
          IsNilpotent (MvPolynomial.coeff (fun₀ | (1 : Fin 2) => 1) (CoeffLineFactor x)) := by
        have hunit' := (MvPolynomial.isUnit_iff.mp hunit).2
        exact hunit' _ hneq
      have hcontr : False := by
        have hnot : ¬ IsNilpotent
            (MvPolynomial.coeff (fun₀ | (1 : Fin 2) => 1) (CoeffLineFactor x)) := by
          simp [hcoeff]
        exact hnot hnil
      exact False.elim hcontr
    · exact Or.inr hq
  · exact Or.inl hp
