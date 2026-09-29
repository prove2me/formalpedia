-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.not_coeffLineFactor_dvd_of_root_left_zero_curry_nonassociated
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:47:04.086766+00:00
-- url     : https://prove2.me/submissions/4b328c7d-1a93-442e-b692-b445c39375af

import Mathlib
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_coeffLineFactor_dvd_of_curry_natDegree_zero_root

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve
namespace PachDeZeeuw.Algebraic

/-- The coefficient-line factor is never a unit. -/
lemma coeffLineFactor_not_isUnit
    (x : ℝ) :
    ¬ IsUnit (CoeffLineFactor x) := by
  intro h
  have hne : (Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ 0 := by
    simp
  have hcoeff :
      MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 1) (CoeffLineFactor x) = 1 := by
    have hCcoeff :
        MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 1) (MvPolynomial.C x) = 0 := by
      rw [MvPolynomial.coeff_C]
      split_ifs with h0
      · exfalso
        exact hne h0.symm
      · rfl
    rw [CoeffLineFactor, MvPolynomial.coeff_sub]
    simp [hCcoeff]
  rcases (MvPolynomial.isUnit_iff.mp h) with ⟨_, hnil⟩
  have hnil1 :
      IsNilpotent
        (MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 1) (CoeffLineFactor x)) := by
    exact hnil _ hne
  rw [hcoeff] at hnil1
  exact not_isNilpotent_one hnil1

/-- A divisor of an irreducible polynomial is associated to it if the divisor is not a unit. -/
lemma associated_of_irreducible_dvd_nonunit
    {R : Type*} [Monoid R] {p d : R}
    (hp : Irreducible p) (hdp : d ∣ p) (hdnu : ¬ IsUnit d) :
    Associated p d := by
  rcases hp.dvd_iff.mp hdp with hdunit | hassoc
  · exact False.elim (hdnu hdunit)
  · exact hassoc

end PachDeZeeuw.Algebraic

open PachDeZeeuw.Algebraic in
theorem solution (h k : MvPolynomial (Fin 2) ℝ)
    (hh : Irreducible h) (hk : Irreducible k)
    (hnot : ¬ Associated h k)
    (hdeg0 : (Curry0 h).natDegree = 0)
    {x : ℝ}
    (hxroot : MvPolynomial.eval (fun _ : Fin 1 => x) ((Curry0 h).coeff 0) = 0) :
    ¬ CoeffLineFactor x ∣ k := by
  intro hkdvd
  have hhdvd : CoeffLineFactor x ∣ h :=
    coeffLineFactor_dvd_of_curry_natDegree_zero_root h hdeg0 hxroot
  have hassoc_line : Associated h (CoeffLineFactor x) :=
    associated_of_irreducible_dvd_nonunit hh hhdvd (coeffLineFactor_not_isUnit x)
  have hdiv : h ∣ k := by
    exact (hassoc_line.dvd_iff_dvd_left).2 hkdvd
  exact hnot (hh.associated_of_dvd hk hdiv)
