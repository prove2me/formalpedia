-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_sheetDensity_eq_214530a51d79
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:26.634403+00:00
-- url     : https://prove2.me/submissions/422d8a2f-beb4-4b7b-93b5-3be40f760789

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdMassAt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_h_eq_9af9feb0e0d4
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.StandardDualMassAtPoint
variable {K : Type} [Field K] [NumberField K] {T : Type} [Fintype T] [DecidableEq T]
namespace GroundTheory.Heights₂.Heights.StandardDualMassAtPoint
theorem _root_.solution (hOn : DualPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (hF : ∀ σ, F.metric σ = 1) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) {y : Fin D → ℂ}
    {w : ((k : Unit) → dualBlocks T k) → ℂ} (h : ∃ γ, IsSheet (dualIdeal b) (dualProj b hb) y w γ) :
    sheetDensity (dualIdeal b) (dualProj b hb) (fun _ z => Real.log ((dualLine F b hb).h z))
      (fun _ => 1) y w = maDensity (fun _ : Fin D => gbPot) y := by
  unfold sheetDensity
  rw [dif_pos h, one_mul]
  apply maDensity_congr_of_eventuallyEq
  intro j
  filter_upwards [h.choose_spec.2] with y' hy'
  obtain ⟨-, hmc, hΨ⟩ := hy'
  show Real.log ((dualLine F b hb).h (h.choose y')) = gbPot y'
  rw [h_eq hOn hF b hb hmc, hΨ, gbPot, Fin.sum_univ_succ]
  simp
end GroundTheory.Heights₂.Heights.StandardDualMassAtPoint
