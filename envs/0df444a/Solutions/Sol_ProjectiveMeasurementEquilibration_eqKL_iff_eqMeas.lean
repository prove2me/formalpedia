-- Prove2me | solution 1 for ProjectiveMeasurementEquilibration.eqKL_iff_eqMeas
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T20:30:33.989507+00:00
-- url     : https://prove2.me/submissions/115ba9db-9a92-49d9-bf3a-e2059ff681a2

import Definitions.Def_pme_measurement_conditions
import Theorems.Thm_ProjectiveMeasurementEquilibration_commute_iff_pinching_eq
import Theorems.Thm_ProjectiveMeasurementEquilibration_pinching_isDensityMatrix
import Theorems.Thm_ProjectiveMeasurementEquilibration_relEntropy_pinching_eq_entropy_sub
import Theorems.Thm_ProjectiveMeasurementEquilibration_relEntropy_chain_rule
import Theorems.Thm_ProjectiveMeasurementEquilibration_relEntropy_nonneg_and_eq_zero_iff
import Mathlib.Data.EReal.Operations

open Matrix ProjectiveMeasurementEquilibration

private lemma pinching_fixed {n : Type} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.IsHermitian) (A : Matrix n n ℂ) :
    pinching hX (pinching hX A) = pinching hX A := by
  classical
  let G := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hX.eigenvectorUnitary
  let F := G.symm
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
  have hidem (A : Matrix n n ℂ) : pinching hX (pinching hX A) = pinching hX A := by
    apply F.injective
    change F (pinching hX (pinching hX A)) = F (pinching hX A)
    ext i j
    simp only [hentry]
    by_cases hij : hX.eigenvalues i = hX.eigenvalues j <;> simp [hij]
  exact hidem A

theorem solution {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) (Φ : Matrix n n ℂ → Matrix n n ℂ) :
    EqKL X Φ ↔ EqMeas hX Φ := by
  have hcomm (ρ : Matrix n n ℂ) : X * pinching hX ρ = pinching hX ρ * X :=
    (commute_iff_pinching_eq hX _).mpr (pinching_fixed hX ρ)
  constructor
  · intro h ρ hρ
    obtain ⟨hΦ, hcΦ, hmin⟩ := h ρ hρ
    have hP := pinching_isDensityMatrix hX ρ hρ
    have hle := hmin (pinching hX ρ) hP (hcomm ρ)
    rw [relEntropy_chain_rule hX ρ (Φ ρ) hρ hΦ hcΦ] at hle
    rw [relEntropy_pinching_eq_entropy_sub hX ρ hρ] at hle
    have hzle : relEntropy (pinching hX ρ) (Φ ρ) ≤ 0 := by
      apply (EReal.addLECancellable_coe
        (vonNeumannEntropy (pinching hX ρ) - vonNeumannEntropy ρ)).add_le_add_iff_right.mp
      simpa only [zero_add, add_comm] using hle
    have hn := relEntropy_nonneg_and_eq_zero_iff (pinching hX ρ) (Φ ρ) hP hΦ
    exact (hn.2.mp (le_antisymm hzle hn.1)).symm
  · intro h ρ hρ
    rw [h ρ hρ]
    have hP := pinching_isDensityMatrix hX ρ hρ
    refine ⟨hP, hcomm ρ, ?_⟩
    intro σ hσ hcσ
    rw [relEntropy_chain_rule hX ρ σ hρ hσ hcσ]
    exact le_add_of_nonneg_right (relEntropy_nonneg_and_eq_zero_iff
      (pinching hX ρ) σ hP hσ).1
