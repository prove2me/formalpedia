-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_proj_segre_planePt_9c8c7cf829ad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:44.609636+00:00
-- url     : https://prove2.me/submissions/8e83eee2-1d8b-42de-863f-48716c62dd14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdMassAt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_segre_const_b90202405c1e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_recover_planePt_b75c0350c21e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_dualProj_apply_5ec1a7484f01


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
omit [Fintype T] [DecidableEq T]
namespace GroundTheory.Heights₂.Heights.StandardDualMassAtPoint
theorem _root_.solution {i : ℕ} {F : HermLattice K i} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) (v : Fin i → ℂ) :
    dualProj b hb (segre (dualPlanePt b σ v)) = v := by
  funext j
  simp only [dualProj_apply, segre_const, recover_planePt]
  rw [Finset.sum_eq_single σ (fun τ _ hτ => if_neg hτ) (by simp)]
  exact if_pos rfl
end GroundTheory.Heights₂.Heights.StandardDualMassAtPoint
