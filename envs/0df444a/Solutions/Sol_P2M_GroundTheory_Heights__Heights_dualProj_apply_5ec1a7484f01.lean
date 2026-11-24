-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_dualProj_apply_5ec1a7484f01
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:08.380874+00:00
-- url     : https://prove2.me/submissions/d9afd250-db42-488a-a07d-5bb311ebacfa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T] [DecidableEq T]
omit [Fintype T] [DecidableEq T]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (s : ((k : Unit) → dualBlocks T k) → ℂ) (j : Fin i) :
    dualProj b hb s j = ∑ σ : K →+* ℂ, dualRecover b hb (fun t => s fun _ => t) (σ, j) := by
  simp [dualProj]
  rfl
end GroundTheory.Heights₂.Heights
