-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_sheetDensity_eq_9d629b041c12
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:30.652866+00:00
-- url     : https://prove2.me/submissions/8785c261-fb66-47e9-9d02-370b006ab21c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjStdMassAt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_h_eq_68d4caf462fc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_maDensity_congr_of_eventuallyEq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ProjectiveStandardMassAtPoint
variable {K : Type} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.ProjectiveStandardMassAtPoint
theorem _root_.solution (hOn : ProjPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (hF : ∀ σ, F.metric σ = 1) {y : Fin D → ℂ}
    {w : ((k : Unit) → projBlocks K (D + 1) k) → ℂ}
    (h : ∃ γ, IsSheet (projSpaceIdeal K (D + 1)) projProj y w γ) :
    sheetDensity (projSpaceIdeal K (D + 1)) projProj (fun _ z => Real.log ((latticeLine F).h z))
      (fun _ => 1) y w = maDensity (fun _ : Fin D => gbPot) y := by
  unfold sheetDensity
  rw [dif_pos h, one_mul]
  apply maDensity_congr_of_eventuallyEq
  intro j
  filter_upwards [h.choose_spec.2] with y' hy'
  obtain ⟨-, hmc, hΨ⟩ := hy'
  show Real.log ((latticeLine F).h (h.choose y')) = gbPot y'
  rw [h_eq hOn hF hmc, hΨ, gbPot, Fin.sum_univ_succ]
  simp
end GroundTheory.Heights₂.Heights.ProjectiveStandardMassAtPoint
