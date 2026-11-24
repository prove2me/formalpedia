-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_jacobian_eq_fderiv_apply_78ebb9abef90
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:09.446527+00:00
-- url     : https://prove2.me/submissions/f16e9af8-8407-4b79-8420-f6def9063384

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChangeOfVariablesDegreePiola

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped ContDiff
open MeasureTheory
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
theorem _root_.solution (H : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ)
    (hd : DifferentiableAt ℝ H x) (k l : Fin n) :
    jacobian H x k l = fderiv ℝ (fun y => H y k) x (Pi.single l 1) := by
  have hd' : HasFDerivAt (fun y => H y k) ((ContinuousLinearMap.proj k).comp (fderiv ℝ H x)) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k).hasFDerivAt.comp x
      hd.hasFDerivAt
  rw [hd'.fderiv]; rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
