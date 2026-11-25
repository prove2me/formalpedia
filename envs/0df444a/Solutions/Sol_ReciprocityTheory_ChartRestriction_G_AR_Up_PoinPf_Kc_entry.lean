-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.Kc_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:25:48.296255+00:00
-- url     : https://prove2.me/submissions/dada490a-19d6-4cb0-82c2-27c236fc13fa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_diag_re
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBdIsUpq_blocks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_weight
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
theorem _root_.solution {p q : ℕ} {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq M) (i : Fin q)
    (j : Fin p) : ‖((M.toBlocks₂₂)⁻¹ * M.toBlocks₂₁) i j‖ ≤ 1 := by
  set A := M.toBlocks₂₂ with hA
  set B := M.toBlocks₂₁ with hB
  have hAB : A * Aᴴ = 1 + B * Bᴴ := (sumBdIsUpq_blocks h).2.2.2
  have hU : IsUnit A.det := isUnit_iff_ne_zero.2 (sumBd_weight h).1
  have hK : (A⁻¹ * B) * (A⁻¹ * B)ᴴ = 1 - A⁻¹ * (A⁻¹)ᴴ := by
    have e1 : B * Bᴴ = A * Aᴴ - 1 := by rw [hAB]; abel
    have e2 : Aᴴ * (A⁻¹)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hU, Matrix.conjTranspose_one]
    calc (A⁻¹ * B) * (A⁻¹ * B)ᴴ = A⁻¹ * (B * Bᴴ) * (A⁻¹)ᴴ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = A⁻¹ * A * (Aᴴ * (A⁻¹)ᴴ) - A⁻¹ * (A⁻¹)ᴴ := by
          rw [e1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 - A⁻¹ * (A⁻¹)ᴴ := by rw [e2, Matrix.nonsing_inv_mul _ hU, Matrix.mul_one]
  have hdiag := congrArg (fun C => (C i i).re) hK
  rw [diag_re, Matrix.sub_apply, Complex.sub_re, diag_re, Matrix.one_apply_eq, Complex.one_re] at hdiag
  have hnn : 0 ≤ ∑ l, Complex.normSq ((A⁻¹) i l) := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hle : Complex.normSq ((A⁻¹ * B) i j) ≤ ∑ l, Complex.normSq ((A⁻¹ * B) i l) :=
    Finset.single_le_sum (f := fun l => Complex.normSq ((A⁻¹ * B) i l))
      (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
  have h1 : ‖(A⁻¹ * B) i j‖ ^ 2 ≤ 1 := by rw [← Complex.normSq_eq_norm_sq]; linarith
  nlinarith [norm_nonneg ((A⁻¹ * B) i j)]
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
