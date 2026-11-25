-- Prove2me | solution 1 for PIW.HCFdeg.polar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:35:17.594956+00:00
-- url     : https://prove2.me/submissions/fcc06255-1955-49b2-98d5-279881dec9a0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Unimod
import Theorems.Thm_PIW_HCFdeg_toM_mkU
import Theorems.Thm_PIW_HCFdeg_toM_mul
import Theorems.Thm_PIW_HCFdeg_toM_inv
import Theorems.Thm_PIW_HCFdeg_inUJ_mul_J_conj
import Theorems.Thm_PI_UpqRep_mem_KG


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open MeasureTheory PI.UpqRep Matrix
open scoped MatrixOrder NNReal ENNReal ComplexOrder Pointwise
variable {n : ℕ} (ε : Fin n → Bool)
namespace PIW.HCFdeg
theorem _root_.solution (g : UJ ε) : ∃ s : UJ ε, (toM s)ᴴ = toM s ∧ g * s⁻¹ ∈ KG ε := by
  set G := toM g with hG
  set P := Gᴴ * G with hPdef
  have hP : 0 ≤ P := (posSemidef_conjTranspose_mul_self G).nonneg
  set s := CFC.sqrt P with hsdef
  have hs0 : 0 ≤ s := CFC.sqrt_nonneg P
  have hss : s * s = P := CFC.sqrt_mul_sqrt_self P hP
  have hsH : sᴴ = s := hs0.posSemidef.isHermitian.eq
  have hJ := Jm_mul_self ε
  have hJH := Jm_conjTranspose ε
  have hPJP : P * Jm ε * P = Jm ε := by
    have := inUJ_mul_J_conj ε g.2
    calc P * Jm ε * P = Gᴴ * (G * Jm ε * Gᴴ) * G := by simp only [hPdef, Matrix.mul_assoc]
      _ = Jm ε := by rw [this]; exact g.2
  have hPi : P⁻¹ = Jm ε * P * Jm ε := by
    apply Matrix.inv_eq_left_inv
    calc Jm ε * P * Jm ε * P = Jm ε * (P * Jm ε * P) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPJP, hJ]
  set w := Jm ε * s * Jm ε with hw
  have hw0 : 0 ≤ w := by
    have := hs0.posSemidef.conjTranspose_mul_mul_same (Jm ε)
    rw [hJH] at this
    exact this.nonneg
  have hJPJ0 : 0 ≤ Jm ε * P * Jm ε := by
    have := hP.posSemidef.conjTranspose_mul_mul_same (Jm ε)
    rw [hJH] at this
    exact this.nonneg
  have hww : w * w = Jm ε * P * Jm ε := by
    calc w * w = Jm ε * s * (Jm ε * Jm ε) * s * Jm ε := by simp only [hw, Matrix.mul_assoc]
      _ = Jm ε * P * Jm ε := by rw [hJ, Matrix.mul_one, ← hss]; simp only [Matrix.mul_assoc]
  have hsq : CFC.sqrt (Jm ε * P * Jm ε) = w := (CFC.sqrt_eq_iff _ _ hJPJ0 hw0).2 hww
  have hsinv : s⁻¹ = w := by
    rw [hsdef, hP.posSemidef.inv_sqrt, hPi, hsq]
  have hdetP : IsUnit P.det := Matrix.isUnit_det_of_right_inverse (B := Jm ε * P * Jm ε) (by
    calc P * (Jm ε * P * Jm ε) = (P * Jm ε * P) * Jm ε := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPJP, hJ])
  have hdets : IsUnit s.det := by
    rw [← hss, Matrix.det_mul] at hdetP
    exact isUnit_of_mul_isUnit_left hdetP
  have hsw : s * w = 1 := by rw [← hsinv]; exact Matrix.mul_nonsing_inv s hdets
  have hsJs : s * Jm ε * s = Jm ε := by
    calc s * Jm ε * s = (s * w) * Jm ε := by simp only [hw, Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = Jm ε := by rw [hsw, Matrix.one_mul]
  have hws : w * s = 1 := by
    calc w * s = Jm ε * (s * Jm ε * s) := by simp only [hw, Matrix.mul_assoc]
      _ = 1 := by rw [hsJs, hJ]
  have hsU : inUJ ε s := by unfold inUJ; rw [hsH]; exact hsJs
  refine ⟨mkU ε s hsU, hsH, ?_⟩
  rw [mem_KG]
  set M := toM (g * (mkU ε s hsU)⁻¹) with hM
  have hMw : M = G * w := by
    rw [hM, toM_mul, toM_inv, toM_mkU, hsH]
  have hMU : Mᴴ * M = 1 := by
    have hwH : wᴴ = w := hw0.posSemidef.isHermitian.eq
    rw [hMw, Matrix.conjTranspose_mul, hwH]
    calc w * Gᴴ * (G * w) = w * (s * s) * w := by rw [hss]; simp only [hPdef, Matrix.mul_assoc]
      _ = (w * s) * (s * w) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hws, hsw, Matrix.mul_one]
  have hMJ : Mᴴ * Jm ε * M = Jm ε := (g * (mkU ε s hsU)⁻¹).2
  refine ⟨Matrix.mem_unitaryGroup_iff'.mpr (by rw [Matrix.star_eq_conjTranspose]; exact hMU), ?_⟩
  have hMM : M * Mᴴ = 1 := mul_eq_one_comm.mp hMU
  calc M * Jm ε = M * (Mᴴ * Jm ε * M) := by rw [hMJ]
    _ = (M * Mᴴ) * Jm ε * M := by simp only [Matrix.mul_assoc]
    _ = Jm ε * M := by rw [hMM, Matrix.one_mul]
end PIW.HCFdeg
