-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_planePt_injective_171c08794023
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:19:21.089302+00:00
-- url     : https://prove2.me/submissions/3d98e47d-7fa1-4a68-8f92-f9c77ff209eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdMassAt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_segre_const_b90202405c1e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_recover_planePt_b75c0350c21e

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
theorem _root_.solution {D : ℕ} {F : HermLattice K (D + 1)} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (y : Fin D → ℂ) :
    Function.Injective fun σ : K →+* ℂ => segre (ι := dualBlocks T) (dualPlanePt b σ (Fin.cons 1 y)) := by
  intro σ τ h
  have h1 := congrArg (fun w : ((k : Unit) → dualBlocks T k) → ℂ =>
    dualRecover b hb (fun t => w fun _ => t)) h
  simp only [segre_const, recover_planePt] at h1
  have h2 := congrFun h1 (σ, 0)
  simpa using h2
end GroundTheory.Heights₂.Heights.StandardDualMassAtPoint
