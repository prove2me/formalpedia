-- Prove2me | solution 1 for ProjectiveMeasurementEquilibration.commute_iff_pinching_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T18:56:48.915016+00:00
-- url     : https://prove2.me/submissions/c74af03e-baf5-4aa8-bc91-646ca1a13859

import Definitions.Def_pme_quantum_basics

open Matrix ProjectiveMeasurementEquilibration

theorem solution {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) (σ : Matrix n n ℂ) :
    X * σ = σ * X ↔ pinching hX σ = σ := by
  classical
  let G := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hX.eigenvectorUnitary
  let F := G.symm
  let D : ℝ → Matrix n n ℂ := fun x =>
    diagonal (fun i => if hX.eigenvalues i = x then (1 : ℂ) else 0)
  have hFX : F X = diagonal (fun i => (hX.eigenvalues i : ℂ)) := by
    simpa [F, G, Function.comp_def] using hX.conjStarAlgAut_star_eigenvectorUnitary
  have heig (x : ℝ) : F (eigenproj hX x) = D x := by
    change G.symm (G (D x)) = D x
    exact G.symm_apply_apply (D x)
  have hpinch : F (pinching hX σ) =
      ∑ x ∈ eigenvalueSet hX, D x * F σ * D x := by
    simp only [pinching, map_sum, map_mul, heig]
  have hentry (i j : n) : F (pinching hX σ) i j =
      if hX.eigenvalues i = hX.eigenvalues j then F σ i j else 0 := by
    rw [hpinch]
    have hmem : hX.eigenvalues j ∈ eigenvalueSet hX :=
      Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    simp [D, Matrix.sum_apply, hmem, eq_comm]
  constructor
  · intro h
    apply F.injective
    change F (pinching hX σ) = F σ
    ext i j
    rw [hentry]
    by_cases hij : hX.eigenvalues i = hX.eigenvalues j
    · simp [hij]
    · have hmul : (hX.eigenvalues i : ℂ) * F σ i j =
          F σ i j * (hX.eigenvalues j : ℂ) := by
        have hc := congrArg (fun M : Matrix n n ℂ => F M i j) h
        simpa only [map_mul, hFX, diagonal_mul, mul_diagonal] using hc
      have hdiff : ((hX.eigenvalues i : ℂ) - (hX.eigenvalues j : ℂ)) * F σ i j = 0 := by
        rw [sub_mul, mul_comm (hX.eigenvalues j : ℂ)]
        exact sub_eq_zero.mpr hmul
      have hzero : F σ i j = 0 := (mul_eq_zero.mp hdiff).resolve_left
        (sub_ne_zero.mpr (Complex.ofReal_injective.ne hij))
      simp [hij, hzero]
  · intro h
    apply F.injective
    change F (X * σ) = F (σ * X)
    simp only [map_mul, hFX]
    ext i j
    simp only [diagonal_mul, mul_diagonal]
    have hblock : (if hX.eigenvalues i = hX.eigenvalues j then F σ i j else 0) =
        F σ i j := by
      simpa only [hentry] using congrArg (fun M : Matrix n n ℂ => F M i j) h
    by_cases hij : hX.eigenvalues i = hX.eigenvalues j
    · rw [hij]
      exact mul_comm _ _
    · have hzero : F σ i j = 0 := by simpa [hij] using hblock.symm
      simp [hzero]
