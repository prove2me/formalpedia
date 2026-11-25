-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_LUB___injOn_52a971afe586
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:21:05.46486+00:00
-- url     : https://prove2.me/submissions/b4383445-5c90-4e31-9f2b-61016b802faf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LocalUnfoldPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUB_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
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
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app
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


section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')
private theorem eq_of_unipotent_lower_mul_eq_upper {n : ℕ} (A C B1 B2 N1 N2 : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A.det)
    (hB1 : IsUnit B1.det) (hB2 : IsUnit B2.det) (hB1t : B1.BlockTriangular id) (hB2t : B2.BlockTriangular id)
    (hN1t : N1.BlockTriangular OrderDual.toDual) (hN2t : N2.BlockTriangular OrderDual.toDual)
    (hd1 : ∀ a, N1 a a = 1) (hd2 : ∀ a, N2 a a = 1) (h1 : A * N1 = C * B1) (h2 : A * N2 = C * B2) :
    N1 = N2 := by
  have hN2u : IsUnit N2.det := by
    rw [Matrix.det_of_lowerTriangular N2 hN2t]
    simp [hd2]
  have h3 : N1 * B1⁻¹ = N2 * B2⁻¹ := by
    have e : A * (N1 * B1⁻¹) = A * (N2 * B2⁻¹) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, h2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB1,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB2]
    have e' := congrArg (fun M => A⁻¹ * M) e
    rwa [Matrix.nonsing_inv_mul_cancel_left _ _ hA, Matrix.nonsing_inv_mul_cancel_left _ _ hA] at e'
  have hk : N2⁻¹ * N1 = B2⁻¹ * B1 := by
    have e3 : N1 = N1 * B1⁻¹ * B1 := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB1, Matrix.mul_one]
    rw [e3, h3, Matrix.mul_assoc N2, ← Matrix.mul_assoc N2⁻¹, Matrix.nonsing_inv_mul _ hN2u, Matrix.one_mul]
  have hPlow : (N2⁻¹ * N1).BlockTriangular OrderDual.toDual := by
    haveI := Matrix.invertibleOfIsUnitDet N2 hN2u
    exact (Matrix.blockTriangular_inv_of_blockTriangular hN2t).mul hN1t
  have hPup : (N2⁻¹ * N1).BlockTriangular id := by
    haveI := Matrix.invertibleOfIsUnitDet B2 hB2
    rw [hk]
    exact (Matrix.blockTriangular_inv_of_blockTriangular hB2t).mul hB1t
  have hoff : ∀ a c, a ≠ c → (N2⁻¹ * N1) a c = 0 := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with h | h
    · exact hPlow (show OrderDual.toDual c < OrderDual.toDual a from h)
    · exact hPup h
  have hN1 : N1 = N2 * (N2⁻¹ * N1) := (Matrix.mul_nonsing_inv_cancel_left N2 N1 hN2u).symm
  have hsum : ∀ a c, (N2 * (N2⁻¹ * N1)) a c = N2 a c * (N2⁻¹ * N1) c c := by
    intro a c
    rw [Matrix.mul_apply, Finset.sum_eq_single c (fun k _ hk => by rw [hoff k c hk, mul_zero]) (by simp)]
  have hPd : ∀ c, (N2⁻¹ * N1) c c = 1 := by
    intro c
    have e := congrFun (congrFun hN1 c) c
    rw [hsum, hd1, hd2, one_mul] at e
    exact e.symm
  ext a c
  have e := congrFun (congrFun hN1 a) c
  rw [hsum, hPd, mul_one] at e
  exact e
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
theorem _root_.solution (hx1 : rmul x1' b1 ∈ X.dom) :
    Set.InjOn (Φ X b1 D) {z | cpt X (rmul x1' b1) z ∈ ExtFPf.cell D} := by
  intro z1 hz1 z2 hz2 hΦ
  obtain ⟨-, hB1, e1⟩ := split X b1 D hz1
  obtain ⟨-, hB2, e2⟩ := split X b1 D hz2
  rw [hΦ] at e1
  have hlow : ∀ (z : V (nd X)) (τ : X.Ψ), (mat (nmat X z) τ).BlockTriangular OrderDual.toDual := by
    intro z τ a c hac
    have hac' : a < c := hac
    simp [mat, nmat, not_lt.2 hac'.le, hac'.ne]
  have hdiag : ∀ (z : V (nd X)) (τ : X.Ψ) (a : Fin r), mat (nmat X z) τ a a = 1 := by
    intro z τ a
    simp [mat, nmat]
  have hup : ∀ b ∈ Bor X.Ψ r, ∀ τ : X.Ψ, (mat b τ).BlockTriangular id := by
    intro b hb τ a c hac
    exact (hb τ).2 a c hac
  have hN : ∀ τ, mat (nmat X z1) τ = mat (nmat X z2) τ := by
    intro τ
    exact eq_of_unipotent_lower_mul_eq_upper (mat (rmul x1' b1) τ) (mat (cpt X x1' (Φ X b1 D z2)) τ) (mat (β X b1 D z1) τ)
      (mat (β X b1 D z2) τ) _ _ (isUnit_iff_ne_zero.2 (hx1 τ).1) (isUnit_iff_ne_zero.2 (hB1 τ).1)
      (isUnit_iff_ne_zero.2 (hB2 τ).1) (hup _ hB1 τ) (hup _ hB2 τ) (hlow z1 τ) (hlow z2 τ)
      (hdiag z1 τ) (hdiag z2 τ) (congrFun e1 τ) (congrFun e2 τ)
  ext i
  obtain ⟨⟨τ, ⟨⟨a, c⟩, hac⟩⟩, rfl⟩ : ∃ e : Ent X, Fintype.equivFin (Ent X) e = i :=
    ⟨(Fintype.equivFin (Ent X)).symm i, (Fintype.equivFin (Ent X)).apply_symm_apply i⟩
  have e := congrFun (congrFun (hN τ) a) c
  simpa [mat, nmat, hac] using e
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
