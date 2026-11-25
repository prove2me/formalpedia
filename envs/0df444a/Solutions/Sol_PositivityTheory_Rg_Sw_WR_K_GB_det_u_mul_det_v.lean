-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.det_u_mul_det_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:28:50.77618+00:00
-- url     : https://prove2.me/submissions/f5f0ee52-5d73-4278-aa83-0c0e3283b6d4

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBFinal
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_dP_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_herm_mem_Ugood

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) :
    (uM s y).det * (vM s y).det = (((dP y : ℝ) : ℂ))⁻¹ := by
  obtain ⟨lam, -, hdP, -⟩ := dP_eq y
  have hg := herm_mem_Ugood s hs y
  have hprod : ((1 : Mc n) - (Complex.I * s) • herm y) * (1 + (Complex.I * s) • herm y) = 1 + herm y * herm y := by
    have hs2 : (Complex.I * s) * (Complex.I * s) = -1 := by
      rcases hs with rfl | rfl <;> simp [← sq, Complex.I_sq] <;> ring_nf <;> simp [Complex.I_sq]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs2]
    simp [neg_smul]; abel
  have h1 := Matrix.det_nonsing_inv_mul_det (A := (1 : Mc n) - (Complex.I * s) • herm y) hg.1
  have h2 := Matrix.det_nonsing_inv_mul_det (A := (1 : Mc n) + (Complex.I * s) • herm y) hg.2
  rw [hdP, ← hprod, Matrix.det_mul]
  simp only [uM, vM]
  apply eq_inv_of_mul_eq_one_left
  calc ((1 - (Complex.I * s) • herm y)⁻¹).det * ((1 + (Complex.I * s) • herm y)⁻¹).det *
        ((1 - (Complex.I * s) • herm y).det * (1 + (Complex.I * s) • herm y).det)
      = (((1 - (Complex.I * s) • herm y)⁻¹).det * (1 - (Complex.I * s) • herm y).det) *
        (((1 + (Complex.I * s) • herm y)⁻¹).det * (1 + (Complex.I * s) • herm y).det) := by ring
    _ = 1 := by rw [h1, h2, one_mul]
end PositivityTheory.Rg.Sw.WR.K.GB
