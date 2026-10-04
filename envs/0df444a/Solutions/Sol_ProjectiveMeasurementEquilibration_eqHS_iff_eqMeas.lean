-- Prove2me | solution 1 for ProjectiveMeasurementEquilibration.eqHS_iff_eqMeas
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T19:10:00.956002+00:00
-- url     : https://prove2.me/submissions/08fee9ef-7674-47e5-9774-95656abda829

import Definitions.Def_pme_measurement_conditions
import Theorems.Thm_ProjectiveMeasurementEquilibration_commute_iff_pinching_eq
import Theorems.Thm_ProjectiveMeasurementEquilibration_pinching_isDensityMatrix
import Theorems.Thm_ProjectiveMeasurementEquilibration_hsDistSq_pythagoras

open Matrix ProjectiveMeasurementEquilibration
open scoped ComplexOrder

theorem solution {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) (Φ : Matrix n n ℂ → Matrix n n ℂ) :
    EqHS X Φ ↔ EqMeas hX Φ := by
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
  have hcomm (A : Matrix n n ℂ) : X * pinching hX A = pinching hX A * X :=
    (commute_iff_pinching_eq hX (pinching hX A)).mpr (hidem A)
  have hnonneg (A B : Matrix n n ℂ) : 0 ≤ hsDistSq A B := by
    exact (RCLike.nonneg_iff.mp (posSemidef_conjTranspose_mul_self (A - B)).trace_nonneg).1
  have hzero (A B : Matrix n n ℂ) (hz : hsDistSq A B = 0) : A = B := by
    have hp := (RCLike.nonneg_iff.mp
      (posSemidef_conjTranspose_mul_self (A - B)).trace_nonneg).2
    have ht : ((A - B)ᴴ * (A - B)).trace = 0 := Complex.ext hz hp
    exact sub_eq_zero.mp (trace_conjTranspose_mul_self_eq_zero_iff.mp ht)
  constructor
  · intro h ρ hρ
    obtain ⟨hΦdensity, hΦcomm, hmin⟩ := h ρ hρ
    have hPdensity := pinching_isDensityMatrix hX ρ hρ
    have hminP := hmin (pinching hX ρ) hPdensity (hcomm ρ)
    have hpyth := hsDistSq_pythagoras hX ρ (Φ ρ) hΦcomm
    have hle : hsDistSq ρ (pinching hX ρ) + hsDistSq (pinching hX ρ) (Φ ρ) ≤
        hsDistSq ρ (pinching hX ρ) := by
      rw [← hpyth]
      exact hminP
    have hzle : hsDistSq (pinching hX ρ) (Φ ρ) ≤ 0 :=
      (add_le_add_iff_left (hsDistSq ρ (pinching hX ρ))).mp (by simpa using hle)
    have hz : hsDistSq (pinching hX ρ) (Φ ρ) = 0 :=
      le_antisymm hzle (hnonneg _ _)
    exact (hzero _ _ hz).symm
  · intro h ρ hρ
    have heq := h ρ hρ
    rw [heq]
    refine ⟨pinching_isDensityMatrix hX ρ hρ, hcomm ρ, ?_⟩
    intro σ hσdensity hσcomm
    rw [hsDistSq_pythagoras hX ρ σ hσcomm]
    exact le_add_of_nonneg_right (hnonneg _ _)
