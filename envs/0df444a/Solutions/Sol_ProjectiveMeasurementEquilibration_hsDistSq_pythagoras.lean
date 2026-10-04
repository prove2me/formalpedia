-- Prove2me | solution 1 for ProjectiveMeasurementEquilibration.hsDistSq_pythagoras
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T19:02:04.878682+00:00
-- url     : https://prove2.me/submissions/1e6252f9-f61d-4341-ace3-da811136a3e0

import Definitions.Def_pme_quantum_basics
import Theorems.Thm_ProjectiveMeasurementEquilibration_commute_iff_pinching_eq

open Matrix ProjectiveMeasurementEquilibration

theorem solution {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) (ρ σ : Matrix n n ℂ) (hσ : X * σ = σ * X) :
    hsDistSq ρ σ = hsDistSq ρ (pinching hX ρ) + hsDistSq (pinching hX ρ) σ := by
  classical
  let G := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hX.eigenvectorUnitary
  let F := G.symm
  let U : Matrix n n ℂ := hX.eigenvectorUnitary
  let D : ℝ → Matrix n n ℂ := fun x =>
    diagonal (fun i => if hX.eigenvalues i = x then (1 : ℂ) else 0)
  have heig (x : ℝ) : F (eigenproj hX x) = D x := by
    change G.symm (G (D x)) = D x
    exact G.symm_apply_apply (D x)
  have hentry (A : Matrix n n ℂ) (i j : n) : F (pinching hX A) i j =
      if hX.eigenvalues i = hX.eigenvalues j then F A i j else 0 := by
    have hpinch : F (pinching hX A) =
        ∑ x ∈ eigenvalueSet hX, D x * F A * D x := by
      simp only [pinching, map_sum, map_mul, heig]
    rw [hpinch]
    have hmem : hX.eigenvalues j ∈ eigenvalueSet hX :=
      Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    simp [D, Matrix.sum_apply, hmem, eq_comm]
  have htrace (A : Matrix n n ℂ) : (F A).trace = A.trace := by
    change (Uᴴ * A * U).trace = A.trace
    have hu : U * Uᴴ = 1 :=
      Unitary.mul_star_self_of_mem hX.eigenvectorUnitary.property
    rw [Matrix.trace_mul_cycle, hu, one_mul]
  have hstar (A : Matrix n n ℂ) : F Aᴴ = (F A)ᴴ := map_star F A
  have hdist (A B : Matrix n n ℂ) : hsDistSq A B = hsDistSq (F A) (F B) := by
    unfold hsDistSq
    rw [← htrace ((A - B)ᴴ * (A - B))]
    simp only [map_mul, map_sub, hstar]
  have hcoord (A B : Matrix n n ℂ) : hsDistSq A B =
      ∑ i : n, ∑ j : n, (star (A j i - B j i) * (A j i - B j i)).re := by
    simp [hsDistSq, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hfix : pinching hX σ = σ := (commute_iff_pinching_eq hX σ).mp hσ
  calc
    hsDistSq ρ σ = hsDistSq (F ρ) (F σ) := hdist ρ σ
    _ = hsDistSq (F ρ) (F (pinching hX ρ)) +
        hsDistSq (F (pinching hX ρ)) (F σ) := by
      rw [hcoord, hcoord, hcoord, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [hentry]
      by_cases hij : hX.eigenvalues j = hX.eigenvalues i
      · simp [hij]
      · have hs0 : F σ j i = 0 := by
          have hc := congrArg (fun A : Matrix n n ℂ => F A j i) hfix
          simpa only [hentry, if_neg hij] using hc.symm
        simp [hij, hs0]
    _ = hsDistSq ρ (pinching hX ρ) + hsDistSq (pinching hX ρ) σ := by
      rw [← hdist ρ (pinching hX ρ), ← hdist (pinching hX ρ) σ]
