-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P75.conjectureOne
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:00:54.290059+00:00
-- url     : https://prove2.me/submissions/04c3633e-d2d8-4576-82e7-1ebba02802f4

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_widthSdpAnnihilator
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_finiteTensorWidths
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_betaInfimalWidth
noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

namespace X6P75C1

open QAlgorithms.Papers.Independent.Information100.P75

lemma phase_zero : phase 0 = 1 := by simp [phase]

lemma blend_zero {ι : Type*} (P Q : Mat ι) : blend 0 P Q = P + Q := by
  simp [blend, phase_zero]

/-- `Ω_0` is exactly the set of density matrices -/
lemma mem_omega_zero {ι : Type*} [Fintype ι] (R : Mat ι) :
    R ∈ omega (ι := ι) 0 ↔ QAlgorithms.IsDensityMatrix R := by
  constructor
  · rintro ⟨-, -, P, Q, hP, hQ, htr, rfl⟩
    rw [blend_zero]
    exact ⟨hP.add hQ, by rw [Matrix.trace_add]; exact htr⟩
  · rintro ⟨hR, htr⟩
    refine ⟨le_rfl, Real.pi_pos, R, 0, hR, Matrix.PosSemidef.zero, by simpa using htr, ?_⟩
    rw [blend_zero, add_zero]

theorem main (N : ℕ) (hN : 1 ≤ N) (b : ℝ) (hb : Real.pi / 2 ≤ b) (hbp : b ≤ Real.pi) :
    (∃ R : Mat (Fin N → Fin 3), QAlgorithms.IsDensityMatrix R ∧
      ∀ X ∈ tensorPower (betaSpace b) N, (Rᴴ * X).trace = 0) ↔
    Real.pi / 2 + Real.pi / (2 * (N : ℝ)) ≤ b ∧ b ≤ Real.pi := by
  set M := tensorPower (betaSpace b) N
  -- the tensor power is the list tensor space of constant factors
  have hM : M = listTensorSpace (fun _ : Fin N => 3) (fun _ => betaSpace b) := rfl
  have hw : infWidth M = min (N * (2 * b - Real.pi)) Real.pi := by
    rw [hM, (finiteTensorWidths hN (fun _ : Fin N => 3) (fun _ => by norm_num)).1,
      betaInfimalWidth b hb hbp]
    simp [mul_sub]
  have h2 := ((widthSdpAnnihilator M 0 le_rfl Real.pi_pos).1.trans
    (widthSdpAnnihilator M 0 le_rfl Real.pi_pos).2)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have e1 : (∃ R : Mat (Fin N → Fin 3), QAlgorithms.IsDensityMatrix R ∧
      ∀ X ∈ M, (Rᴴ * X).trace = 0) ↔ ∃ R ∈ omega (ι := Fin N → Fin 3) 0, ∀ X ∈ M,
        (R * X).trace = 0 := by
    constructor
    · rintro ⟨R, hR, hRX⟩
      refine ⟨R, (mem_omega_zero R).2 hR, fun X hX => ?_⟩
      have := hRX X hX
      rwa [hR.1.isHermitian.eq] at this
    · rintro ⟨R, hR, hRX⟩
      have hR' := (mem_omega_zero R).1 hR
      refine ⟨R, hR', fun X hX => ?_⟩
      rw [hR'.1.isHermitian.eq]; exact hRX X hX
  rw [e1, ← h2, add_zero, hw]
  constructor
  · intro h
    refine ⟨?_, hbp⟩
    have h' : Real.pi ≤ N * (2 * b - Real.pi) := le_trans h (min_le_left _ _)
    rw [div_add_div _ _ (by norm_num) (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  · rintro ⟨h1, -⟩
    refine le_min ?_ le_rfl
    rw [div_add_div _ _ (by norm_num) (by positivity), div_le_iff₀ (by positivity)] at h1
    nlinarith

end X6P75C1

open QAlgorithms.Papers.Independent.Information100.P75 in
theorem solution (N : ℕ) (hN : 1 ≤ N) (b : ℝ)
    (hb : Real.pi / 2 ≤ b) (hbp : b ≤ Real.pi) :
    (∃ R : Mat (Fin N → Fin 3), QAlgorithms.IsDensityMatrix R ∧
      ∀ X ∈ tensorPower (betaSpace b) N, (Rᴴ * X).trace = 0) ↔
    Real.pi / 2 + Real.pi / (2 * (N : ℝ)) ≤ b ∧ b ≤ Real.pi :=
  X6P75C1.main N hN b hb hbp
