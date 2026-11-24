-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.KU.rmul_mem_S
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:47.263827+00:00
-- url     : https://prove2.me/submissions/f36a6fbd-954a-4e16-8b19-d3a6c2abcb54

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfC
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


section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
private lemma rmul_rmul_eq_rmul_rmul (X : Data E r) (x b c : Frame X.Ψ r) :
    rmul (rmul x b) c = rmul x (rmul b c) := by
  funext τ
  exact Matrix.mul_assoc (mat x τ) (mat b τ) (mat c τ)
private lemma bor_rmul_mem (X : Data E r) {b c : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (hc : c ∈ Bor X.Ψ r) : rmul b c ∈ Bor X.Ψ r := by
  intro τ
  have hm : mat (rmul b c) τ = mat b τ * mat c τ := rfl
  refine ⟨?_, fun a d hda => ?_⟩
  · rw [hm, Matrix.det_mul]
    exact mul_ne_zero (hb τ).1 (hc τ).1
  · have h1 : (mat b τ).BlockTriangular id := fun i j h => (hb τ).2 i j h
    have h2 : (mat c τ).BlockTriangular id := fun i j h => (hc τ).2 i j h
    exact (h1.mul h2) hda
private lemma inv_mat_mem_bor (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) ∈ Bor X.Ψ r := by
  intro τ
  have hu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.mpr (hb τ).1
  have hm : mat (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) τ = (mat b τ)⁻¹ := rfl
  refine ⟨?_, fun a d hda => ?_⟩
  · rw [hm]
    exact (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero
  letI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ hu
  have h1 : (mat b τ).BlockTriangular id := fun i j h => (hb τ).2 i j h
  exact (Matrix.blockTriangular_inv_of_blockTriangular h1) hda
private lemma rmul_rmul_inv_mat (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (y : Frame X.Ψ r) :
    rmul (rmul y b) (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) = y := by
  funext τ
  have hu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.mpr (hb τ).1
  show mat y τ * mat b τ * (mat b τ)⁻¹ = y τ
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  rfl
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
attribute [local instance] ReciprocityTheory.ChartRestriction.G.AR.Up.KU.instMSMat
attribute [local instance] ReciprocityTheory.ChartRestriction.G.AR.Up.KU.instBorelMat
attribute [local instance] ReciprocityTheory.ChartRestriction.G.AR.Up.KU.instSCMat
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
attribute [local instance] ReciprocityTheory.ChartRestriction.G.AR.Up.KU.instPolishFrame
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU
theorem _root_.solution (X : Data E r) {x0 : Frame X.Ψ r} {FF : Set (V (nd X))} {y b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : rmul y b ∈ Sset X x0 FF ↔ y ∈ Sset X x0 FF := by
  constructor
  · rintro ⟨⟨z, c⟩, ⟨hz, hc⟩, h⟩
    refine ⟨⟨z, rmul c (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)⟩, ⟨hz, bor_rmul_mem X hc (inv_mat_mem_bor X hb)⟩, ?_⟩
    simp only at h ⊢
    exact (rmul_rmul_eq_rmul_rmul X _ _ _).symm.trans
      ((congrArg (fun w => rmul w _) h).trans (rmul_rmul_inv_mat X hb y))
  · rintro ⟨⟨z, c⟩, ⟨hz, hc⟩, h⟩
    refine ⟨⟨z, rmul c b⟩, ⟨hz, bor_rmul_mem X hc hb⟩, ?_⟩
    simp only at h ⊢
    exact (rmul_rmul_eq_rmul_rmul X _ _ _).symm.trans (congrArg (fun w => rmul w b) h)
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
