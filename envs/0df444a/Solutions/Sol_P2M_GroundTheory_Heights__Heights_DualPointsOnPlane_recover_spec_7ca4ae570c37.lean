-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_recover_spec_7ca4ae570c37
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:24.739004+00:00
-- url     : https://prove2.me/submissions/3274cee9-083d-4004-bf05-9132283cfdb9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOnPlane

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
open GroundTheory.Heights₂.Heights.DualPointsOnPlane
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T]
omit [Fintype T]
namespace GroundTheory.Heights₂.Heights.DualPointsOnPlane
theorem _root_.solution (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (Z : T → ℂ) (t : T) :
    Z t = ∑ p : (K →+* ℂ) × Fin i, p.1 ((b t : Fin i → K) p.2) * dualRecover b hb Z p := by
  have h := (LinearEquiv.ofBijective (Matrix.mulVecLin (dualEmbMatrix b)) hb).apply_symm_apply Z
  rw [LinearEquiv.ofBijective_apply, Matrix.mulVecLin_apply] at h
  conv_lhs => rw [← h]
  rfl
end GroundTheory.Heights₂.Heights.DualPointsOnPlane
