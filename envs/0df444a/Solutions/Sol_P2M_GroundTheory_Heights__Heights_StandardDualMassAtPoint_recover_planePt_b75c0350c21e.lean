-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_recover_planePt_b75c0350c21e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:52:00.173505+00:00
-- url     : https://prove2.me/submissions/6a6adac3-8616-4daf-90ec-f24d4e2b6d2d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdMassAt

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
open Classical
namespace GroundTheory.Heights₂.Heights.StandardDualMassAtPoint
theorem _root_.solution {i : ℕ} {F : HermLattice K i} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) (v : Fin i → ℂ) :
    dualRecover b hb (fun t => dualPlanePt b σ v ⟨(), t⟩) =
      fun p => if p.1 = σ then v p.2 else 0 := by
  rw [dualRecover, LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply]
  funext t
  simp [Matrix.mulVec, dotProduct, dualEmbMatrix, dualPlanePt,
    Fintype.sum_prod_type]
end GroundTheory.Heights₂.Heights.StandardDualMassAtPoint
