-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SheetHessPSD_proof_1d484ef0894d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:25:10.839786+00:00
-- url     : https://prove2.me/submissions/de7cc1d9-9865-4d65-bb9c-ffeed6f25218

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSheetHessPSD
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemiPosTwist
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterOsgood
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSheetHessPSD
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_analyticAt_of_eventually_differentiableAt_1dd9a6cb1b42
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_isOpen_noZeroBlock_a770c8a08c0b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_laplacian_line_eq_levi_3ac6aef88d61
import Theorems.Thm_ReciprocityTheory_AnForm_M_hessC_posSemidef
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped ComplexOrder
namespace GroundTheory.Heights₂.Heights.Inter
namespace SheetHessPSD
theorem _root_.solution : SheetHessPSD.Statement := by
  intro K _ ι _ P e Ψ M y w γ hM hPos hγ
  have hev := hγ.2
  have hγy : γ y ∈ mcPts P := hev.self_of_nhds.2.1
  have hz : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := hγy.1
  have han : AnalyticAt ℂ γ y :=
    analyticAt_of_eventually_differentiableAt (hev.mono fun _ h => h.1)
  have hUo := SemipositiveTwist.isOpen_noZeroBlock (ι := ι)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log (M.h z)) (γ y) :=
    ((hM.contDiffAt (hUo.mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)).log (M.pos _ hz).ne'
  have hcomp : (fun y' => Real.log (M.h (γ y'))) = (fun z => Real.log (M.h z)) ∘ γ := rfl
  have hC2 : ContDiffAt ℝ 2 (fun y' => Real.log (M.h (γ y'))) y := by
    rw [hcomp]
    exact hlog.comp y (han.restrictScalars.contDiffAt)
  show (ReciprocityTheory.AnForm.hessC (fun y' => Real.log (M.h (γ y'))) y).PosSemidef
  refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ y hC2 fun x => ?_
  rw [hcomp, ReciprocityTheory.AnForm.levi_comp x han hlog]
  have hL := SemipositiveTwist.laplacian_line_eq_levi hlog (fderiv ℂ γ y x)
  have hΔ := hPos (γ y) hz (fderiv ℂ γ y x)
  linarith
end SheetHessPSD
end GroundTheory.Heights₂.Heights.Inter
