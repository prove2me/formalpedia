-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ortho_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:49:49.419798+00:00
-- url     : https://prove2.me/submissions/eb4f164c-f471-4f3b-bde4-4b8f9ed0a708

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_bOf_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_ortho_bOf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution : OrthoStatement (E := E) := by
  intro r X x hx

  have hBor := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem (X := X) hx
  refine ⟨ReciprocityTheory.ChartRestriction.G.FD.rmul x (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x),
    ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf (X := X) hx,
    fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹ :
      Matrix (Fin r) (Fin r) ℂ), ?_, ?_⟩
  · intro τ
    have hdet : IsUnit (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).det :=
      isUnit_iff_ne_zero.mpr (hBor τ).1
    haveI : Invertible (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ) :=
      Matrix.invertibleOfIsUnitDet _ hdet
    have hM : (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).BlockTriangular id :=
      fun i j hij => (hBor τ).2 i j hij
    have hMi := Matrix.blockTriangular_inv_of_blockTriangular hM
    refine ⟨?_, fun a c hca => hMi hca⟩
    show ((ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹).det ≠ 0
    exact (Matrix.isUnit_nonsing_inv_det _ hdet).ne_zero
  · funext τ
    have hdet : IsUnit (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).det :=
      isUnit_iff_ne_zero.mpr (hBor τ).1
    show ReciprocityTheory.ChartRestriction.G.FD.mat x τ = ReciprocityTheory.ChartRestriction.G.FD.mat x τ *
      ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ *
      (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
end ReciprocityTheory.ChartRestriction.G.AR.Up
