-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.Yd_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:42:54.200037+00:00
-- url     : https://prove2.me/submissions/946faeb7-b66f-495d-b8f4-c761088b24dd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_TelePoint
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoefNonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_Lin_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_Xd_lower
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_nmat_det_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution (b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) (z u : V (nd X)) (hu : u ≠ 0) :
    ∃ τ, ∃ a j : Fin r, (a : ℕ) < j ∧ Yd X b z u τ j a ≠ 0 := by
  obtain ⟨τ, hτ⟩ := Lin_ne X u hu
  refine ⟨τ, ?_⟩
  by_contra hall
  push Not at hall
  apply hτ
  have hN : IsUnit (mat (nmat X z) τ).det := nmat_det_unit X z τ
  have hB : (mat b τ).BlockTriangular id := fun a c hca => (hb τ).2 a c hca
  have hBd : IsUnit (mat b τ).det := isUnit_iff_ne_zero.2 (hb τ).1
  have : Invertible (mat b τ) := (mat b τ).invertibleOfIsUnitDet hBd
  have hY : (Yd X b z u τ).BlockTriangular id := fun a c hca => hall c a hca
  have hX : Xd X z u τ = mat b τ * Yd X b z u τ * (mat b τ)⁻¹ := by
    unfold Yd
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBd, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left _ _ hBd]
  have hXu : (Xd X z u τ).BlockTriangular id := by
    rw [hX]
    exact (hB.mul hY).mul (Matrix.blockTriangular_inv_of_blockTriangular hB)
  have hXd : Xd X z u τ = 0 := by
    ext i j
    rcases lt_or_ge j i with h | h
    · exact hXu h
    · exact Xd_lower X z u τ i j h
  have hLin : KapPf.Lin X τ u = mat (nmat X z) τ * Xd X z u τ := by
    unfold Xd
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hN]
  rw [hLin, hXd, Matrix.mul_zero]
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
