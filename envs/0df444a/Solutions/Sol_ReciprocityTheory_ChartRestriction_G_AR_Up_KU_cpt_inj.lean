-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.KU.cpt_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:54:26.093853+00:00
-- url     : https://prove2.me/submissions/d2b7a7db-fa7d-4874-9b2b-39aded94bae7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_Lemmata_GeneralBFactVariant_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_lu_unique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_nM_low
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_nmat_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_det_nM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_det_ne_of_orth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_nM_diag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_upper_of_bor
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU
theorem _root_.solution (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {z z' : V (nd X)} {b b' : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) (h : rmul (cpt X x0 z) b = rmul (cpt X x0 z') b') :
    z = z' ∧ b = b' := by
  have hN : ∀ τ, ExF.nM X z τ * mat b τ = ExF.nM X z' τ * mat b' τ := by
    intro τ
    have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
    have := congrArg (fun y : Frame X.Ψ r => (mat x0 τ)⁻¹ * mat y τ) h
    rwa [show mat (rmul (cpt X x0 z) b) τ = mat x0 τ * (ExF.nM X z τ * mat b τ) by
        show (mat x0 τ * ExF.nM X z τ) * mat b τ = _; exact Matrix.mul_assoc _ _ _,
      show mat (rmul (cpt X x0 z') b') τ = mat x0 τ * (ExF.nM X z' τ * mat b' τ) by
        show (mat x0 τ * ExF.nM X z' τ) * mat b' τ = _; exact Matrix.mul_assoc _ _ _,
      Matrix.nonsing_inv_mul_cancel_left _ _ hu, Matrix.nonsing_inv_mul_cancel_left _ _ hu] at this
  have hn : ∀ τ, ExF.nM X z τ = ExF.nM X z' τ := fun τ =>
    lu_unique (nM_low X z τ) (nM_low X z' τ) (ExF.nM_diag X z τ) (ExF.nM_diag X z' τ)
      (FrameDegreeData.upper_of_bor X hb τ) (FrameDegreeData.upper_of_bor X hb' τ) (hb τ).1 (hN τ)
  refine ⟨nmat_inj X hn, ?_⟩
  funext τ
  have hu : IsUnit (ExF.nM X z τ).det := by rw [ExF.det_nM]; exact isUnit_one
  have := hN τ
  rw [hn τ] at this
  rw [← hn τ] at this
  have := congrArg (fun M => (ExF.nM X z τ)⁻¹ * M) this
  simp only [Matrix.nonsing_inv_mul_cancel_left _ _ hu] at this
  exact this
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
