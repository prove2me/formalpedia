-- Prove2me | solution 1 for TranscendenceTheory.bivariate_resultant_cyclic_dimension_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T15:07:45.111933+00:00
-- url     : https://prove2.me/submissions/e333d776-5080-4ff5-8c19-605f047b8efd

import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Analysis.Complex.Basic

noncomputable section
open Polynomial
open scoped Classical

private lemma bivariate_resultant_degree (F H : Polynomial (Polynomial ℂ)) (a b : ℕ)
    (hF : ∀ i, (F.coeff i).natDegree ≤ a) (hH : ∀ i, (H.coeff i).natDegree ≤ b) :
    (F.resultant H).natDegree ≤ F.natDegree * b + H.natDegree * a := by
  let m := F.natDegree
  let n := H.natDegree
  let w : Fin (m + n) → ℕ := fun j => j.addCases (fun _ => b) (fun _ => a)
  have hentry (i j : Fin (m + n)) : (F.sylvester H m n i j).natDegree ≤ w j := by
    induction j using Fin.addCases with
    | left j =>
      simp only [sylvester, Matrix.of_apply, w, Fin.addCases_left]
      split_ifs
      · exact hH _
      · simp
    | right j =>
      simp only [sylvester, Matrix.of_apply, w, Fin.addCases_right]
      split_ifs
      · exact hF _
      · simp
  change (F.sylvester H m n).det.natDegree ≤ m * b + n * a
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ hσ
  calc
    _ = (∏ j : Fin (m + n), F.sylvester H m n (σ j) j).natDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign
      · rw [hsign, one_smul]
      · rw [hsign, Units.neg_smul, one_smul, natDegree_neg]
    _ ≤ ∑ j : Fin (m + n), (F.sylvester H m n (σ j) j).natDegree :=
      natDegree_prod_le _ _
    _ ≤ ∑ j : Fin (m + n), w j := Finset.sum_le_sum fun j _ => hentry _ j
    _ = m * b + n * a := by simp [w, Fin.sum_univ_add]

theorem solution
    (A : Type*) [CommRing A] [Algebra ℂ A] (x y : A)
    (F H : Polynomial (Polynomial ℂ)) (a b : ℕ)
    (hF : ∀ i, (F.coeff i).natDegree ≤ a)
    (hH : ∀ i, (H.coeff i).natDegree ≤ b)
    (hdegree : F.natDegree ≠ 0 ∨ H.natDegree ≠ 0)
    (hres : F.resultant H ≠ 0)
    (hFx : F.eval₂ (Polynomial.aeval x).toRingHom y = 0)
    (hHx : H.eval₂ (Polynomial.aeval x).toRingHom y = 0) :
    IsIntegral ℂ x ∧
      Module.finrank ℂ (Algebra.adjoin ℂ ({x} : Set A)) ≤
        F.natDegree * b + H.natDegree * a := by
  obtain ⟨u, v, _, _, huv⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant F H le_rfl le_rfl hdegree
  have heval : Polynomial.aeval x (F.resultant H) = 0 := by
    let φ : Polynomial (Polynomial ℂ) →+* A :=
      Polynomial.eval₂RingHom (Polynomial.aeval x).toRingHom y
    have h := congrArg φ huv
    change φ F = 0 at hFx
    change φ H = 0 at hHx
    rw [map_add, map_mul, map_mul, hFx, hHx, zero_mul, zero_mul, zero_add] at h
    simpa [φ] using h.symm
  have hx : IsIntegral ℂ x := (show IsAlgebraic ℂ x from ⟨F.resultant H, hres, heval⟩).isIntegral
  refine ⟨hx, ?_⟩
  calc
    Module.finrank ℂ (Algebra.adjoin ℂ ({x} : Set A)) = (minpoly ℂ x).natDegree :=
      (Algebra.adjoin.powerBasis hx).finrank
    _ ≤ (F.resultant H).natDegree :=
      Polynomial.natDegree_le_of_dvd ((minpoly.dvd_iff).mpr heval) hres
    _ ≤ F.natDegree * b + H.natDegree * a := bivariate_resultant_degree F H a b hF hH
