-- Prove2me | solution 1 for WolfAreaLaw.thermalState_isDensityMatrix
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:44:17.455666+00:00
-- url     : https://prove2.me/submissions/73aba699-4943-4f1b-b869-77af57b44ee6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_WolfAreaLaw_thermalState

namespace Aux_Wolf_thermal
open scoped ComplexOrder Matrix

theorem herm_smul {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (r : ℝ) :
    ((r : ℂ) • H).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hH.eq]
  congr 1
  simp [Complex.conj_ofReal]

end Aux_Wolf_thermal

open Aux_Wolf_thermal in
open scoped ComplexOrder Matrix in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (β : ℝ) :
    QAlgorithms.IsDensityMatrix (WolfAreaLaw.thermalState β H) := by
  unfold WolfAreaLaw.thermalState QAlgorithms.gibbsState
  set X : Matrix ι ι ℂ := ((-β / 2 : ℝ) : ℂ) • H with hX
  have hXA : X + X = -(β : ℂ) • H := by
    rw [hX, ← add_smul]; congr 1; push_cast; ring
  have hXh : X.IsHermitian := herm_smul H hH _
  have hexp : NormedSpace.exp (-(β : ℂ) • H) =
      (NormedSpace.exp X)ᴴ * NormedSpace.exp X := by
    rw [← hXA, Matrix.exp_add_of_commute X X (Commute.refl X), (hXh.exp).eq]
  have hpsd : (NormedSpace.exp (-(β : ℂ) • H)).PosSemidef := by
    rw [hexp]; exact Matrix.posSemidef_conjTranspose_mul_self _
  set t := (NormedSpace.exp (-(β : ℂ) • H)).trace with ht
  have ht0 : 0 ≤ t := hpsd.trace_nonneg
  have htne : t ≠ 0 := by
    intro h0
    have := (hpsd.trace_eq_zero_iff).mp h0
    have hu := Matrix.isUnit_exp (-(β : ℂ) • H)
    rw [this] at hu
    exact not_isUnit_zero hu
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp ht0
  have htr : t = ((t.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [← him]
  have hpos : 0 < t.re := by
    rcases hre.lt_or_eq with h | h
    · exact h
    · exfalso; apply htne; rw [htr, ← h]; simp
  refine ⟨hpsd.smul ?_, ?_⟩
  · rw [htr, ← Complex.ofReal_inv]
    exact Complex.zero_le_real.mpr (inv_nonneg.mpr hpos.le)
  · rw [Matrix.trace_smul, smul_eq_mul, ← ht, inv_mul_cancel₀ htne]
