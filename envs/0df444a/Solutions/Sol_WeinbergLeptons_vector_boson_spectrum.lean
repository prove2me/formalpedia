-- Prove2me | solution 1 for WeinbergLeptons.vector_boson_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T16:45:25.916736+00:00
-- url     : https://prove2.me/submissions/bd201a09-08e6-4027-b41d-ee6733250aec

import Mathlib
import Definitions.Def_WeinbergLeptons_Model

set_option autoImplicit false

open WeinbergLeptons Matrix in
theorem wl_zdot (g g' : ℝ) (v : Fin 4 → ℝ) :
    zVec g g' ⬝ᵥ v = (g * v 2 + g' * v 3) / Real.sqrt (g ^ 2 + g' ^ 2) := by
  simp [zVec, dotProduct, Fin.sum_univ_four]
  ring

open WeinbergLeptons Matrix in
theorem wl_pdot (g g' : ℝ) (v : Fin 4 → ℝ) :
    photonVec g g' ⬝ᵥ v = (-g' * v 2 + g * v 3) / Real.sqrt (g ^ 2 + g' ^ 2) := by
  simp [photonVec, dotProduct, Fin.sum_univ_four]
  ring

open WeinbergLeptons Matrix in
theorem wl_w_eig (g g' lam : ℝ) :
    (massSqMatrix g g' lam).map (fun x : ℝ => (x : ℂ)) *ᵥ wVec = ((wMass g lam : ℂ) ^ 2) • wVec := by
  ext i
  fin_cases i <;>
    simp [massSqMatrix, wVec, wMass, mulVec, dotProduct, Fin.sum_univ_four] <;> ring

open WeinbergLeptons Matrix in
theorem wl_z_eig (g g' lam : ℝ) :
    massSqMatrix g g' lam *ᵥ zVec g g' = (zMass g g' lam ^ 2) • zVec g g' := by
  have hN2 : Real.sqrt (g ^ 2 + g' ^ 2) ^ 2 = g ^ 2 + g' ^ 2 := Real.sq_sqrt (by positivity)
  ext i
  fin_cases i <;>
    simp [massSqMatrix, zVec, zMass, mulVec, dotProduct, Fin.sum_univ_four]
  · linear_combination (-(lam ^ 2 / 4) * (Real.sqrt (g ^ 2 + g' ^ 2))⁻¹ * g) * hN2
  · linear_combination (-(lam ^ 2 / 4) * (Real.sqrt (g ^ 2 + g' ^ 2))⁻¹ * g') * hN2

open WeinbergLeptons Matrix in
theorem wl_photon_null (g g' lam : ℝ) :
    massSqMatrix g g' lam *ᵥ photonVec g g' = 0 := by
  ext i
  fin_cases i <;>
    simp [massSqMatrix, photonVec, mulVec, dotProduct, Fin.sum_univ_four] <;> ring

open WeinbergLeptons Matrix in
theorem wl_orthonormal (g g' : ℝ) (hN : 0 < g ^ 2 + g' ^ 2) :
    zVec g g' ⬝ᵥ zVec g g' = 1 ∧ photonVec g g' ⬝ᵥ photonVec g g' = 1 ∧
      zVec g g' ⬝ᵥ photonVec g g' = 0 := by
  have hNp : 0 < Real.sqrt (g ^ 2 + g' ^ 2) := Real.sqrt_pos.2 hN
  have hN2 : Real.sqrt (g ^ 2 + g' ^ 2) ^ 2 = g ^ 2 + g' ^ 2 := Real.sq_sqrt hN.le
  have hne : Real.sqrt (g ^ 2 + g' ^ 2) ≠ 0 := hNp.ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [wl_zdot]
    simp [zVec]
    field_simp
    linear_combination -hN2
  · rw [wl_pdot]
    simp [photonVec]
    field_simp
    linear_combination -hN2
  · rw [wl_zdot, div_eq_zero_iff]
    left
    simp only [photonVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val]
    simp
    ring

open WeinbergLeptons Matrix in
theorem wl_charge (g g' : ℝ) (hN : 0 < g ^ 2 + g' ^ 2) (T3 Y : ℝ) (V : Fin 4 → ℝ) :
    g * T3 * V 2 + g' * Y * V 3 =
      -electricCharge g g' * (T3 - Y) * (photonVec g g' ⬝ᵥ V) +
        (g ^ 2 * T3 + g' ^ 2 * Y) / Real.sqrt (g ^ 2 + g' ^ 2) * (zVec g g' ⬝ᵥ V) := by
  have hNp : 0 < Real.sqrt (g ^ 2 + g' ^ 2) := Real.sqrt_pos.2 hN
  have hN2 : Real.sqrt (g ^ 2 + g' ^ 2) ^ 2 = g ^ 2 + g' ^ 2 := Real.sq_sqrt hN.le
  have hi : (Real.sqrt (g ^ 2 + g' ^ 2))⁻¹ * (Real.sqrt (g ^ 2 + g' ^ 2))⁻¹ * (g ^ 2 + g' ^ 2) = 1 := by
    have hne := hNp.ne'
    field_simp
    linarith [hN2]
  rw [wl_zdot, wl_pdot]
  unfold electricCharge
  linear_combination (-(g * T3 * V 2 + g' * Y * V 3)) * hi

open WeinbergLeptons Matrix in
theorem solution (g g' lam : ℝ) (hN : 0 < g ^ 2 + g' ^ 2) :
    (massSqMatrix g g' lam).map (fun x : ℝ => (x : ℂ)) *ᵥ wVec = ((wMass g lam : ℂ) ^ 2) • wVec ∧
    massSqMatrix g g' lam *ᵥ zVec g g' = (zMass g g' lam ^ 2) • zVec g g' ∧
    massSqMatrix g g' lam *ᵥ photonVec g g' = 0 ∧
    zVec g g' ⬝ᵥ zVec g g' = 1 ∧ photonVec g g' ⬝ᵥ photonVec g g' = 1 ∧
    zVec g g' ⬝ᵥ photonVec g g' = 0 ∧
    (∀ T3 Y : ℝ, ∀ V : Fin 4 → ℝ, g * T3 * V 2 + g' * Y * V 3 =
      -electricCharge g g' * (T3 - Y) * (photonVec g g' ⬝ᵥ V) +
        (g ^ 2 * T3 + g' ^ 2 * Y) / Real.sqrt (g ^ 2 + g' ^ 2) * (zVec g g' ⬝ᵥ V)) := by
  obtain ⟨h1, h2, h3⟩ := wl_orthonormal g g' hN
  exact ⟨wl_w_eig g g' lam, wl_z_eig g g' lam, wl_photon_null g g' lam, h1, h2, h3,
    fun T3 Y V => wl_charge g g' hN T3 Y V⟩
