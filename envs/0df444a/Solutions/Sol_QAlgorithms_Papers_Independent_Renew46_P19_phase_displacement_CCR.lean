-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P19.phase_displacement_CCR
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:49:29.169803+00:00
-- url     : https://prove2.me/submissions/ae1a423d-005d-44e7-9bc4-f911af657bc8

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P19
noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

open QAlgorithms.Papers.Independent.Renew46.P19

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates Quadrature)

open QAlgorithms.Papers.Independent.Next46.P20
  (ConfigurationL2 PhaseL2 phasePosition phaseMomentum phasePoint)

open QAlgorithms.Papers.Independent.Claimed50.P05 (spectrumOf pointSpectrum)

open QAlgorithms.Papers.Independent.Frontier30.P10 (symplecticPair)

local notation "sigma" => fun {n : ℕ} (z w : PhaseCoordinates n) =>
  symplecticPair (Sum.elim (phasePosition z) (phaseMomentum z))
    (Sum.elim (phasePosition w) (phaseMomentum w))

theorem g64n_sp_eq {n : ℕ} (z w : PhaseCoordinates n) :
    sigma z w = ∑ j : Fin n, (z (j, 1) * w (j, 0) - z (j, 0) * w (j, 1)) := by
  simp [symplecticPair, phasePosition, phaseMomentum]

theorem g64n_key {n : ℕ} (hbar : ℝ) (d e : PhaseCoordinates n) (f : PhaseCoordinates n → ℂ)
    (z : PhaseCoordinates n) :
    phaseShift hbar d (phaseShift hbar e f) z =
      Complex.exp (Complex.I * ((sigma d e / (2 * hbar) : ℝ) : ℂ)) * phaseShift hbar (d + e) f z := by
  unfold phaseShift
  have harg : z - (1 / 2 : ℝ) • d - (1 / 2 : ℝ) • e = z - (1 / 2 : ℝ) • (d + e) := by
    rw [smul_add]; abel
  rw [harg, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  have hs : sigma (z - (1 / 2 : ℝ) • d) e = sigma z e - sigma d e / 2 := by
    simp only [g64n_sp_eq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hs2 : sigma z (d + e) = sigma z d + sigma z e := by
    simp only [g64n_sp_eq, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hs3 : sigma e d = - sigma d e := by
    simp only [g64n_sp_eq]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hs, hs2]
  by_cases hh : hbar = 0
  · subst hh; simp
  · push_cast
    field_simp
    ring

theorem solution {n : ℕ} (hn : 0 < n) (hbar : ℝ) (hhbar : 0 < hbar)
    (d e : PhaseCoordinates n) (f : PhaseCoordinates n → ℂ) (z : PhaseCoordinates n) :
    phaseShift hbar (d + e) f z =
      Complex.exp (-Complex.I * ((sigma d e / (2 * hbar) : ℝ) : ℂ)) *
        phaseShift hbar d (phaseShift hbar e f) z ∧
    phaseShift hbar e (phaseShift hbar d f) z =
      Complex.exp (-Complex.I * ((sigma d e / hbar : ℝ) : ℂ)) *
        phaseShift hbar d (phaseShift hbar e f) z := by
  have hs3 : sigma e d = - sigma d e := by
    simp only [g64n_sp_eq]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have h1 := g64n_key hbar d e f z
  have h2 := g64n_key hbar e d f z
  rw [add_comm e d, hs3] at h2
  constructor
  · rw [h1, ← mul_assoc, ← Complex.exp_add]
    have : -Complex.I * ((sigma d e / (2 * hbar) : ℝ) : ℂ) +
        Complex.I * ((sigma d e / (2 * hbar) : ℝ) : ℂ) = 0 := by ring
    rw [this, Complex.exp_zero, one_mul]
  · rw [h2, h1, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
