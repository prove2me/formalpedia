-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_sum_fderiv_cofactorFn_eq_zero_8bc35bb39030
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:07:46.897077+00:00
-- url     : https://prove2.me/submissions/f64a947e-e562-4da4-a534-941c4d3ffee6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChangeOfVariablesDegreePiola
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_killRow_apply_self_d76e563b4290
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_killRow_apply_ne_1a887c5f0654
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_hasFDerivAt_cofactorFn_a81428026681
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_sum_det_symm_eq_zero_0eb09c5f9247

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
theorem _root_.solution (H : (Fin n → ℝ) → Fin n → ℝ) (hH : ContDiff ℝ ∞ H) (i : Fin n)
    (x : Fin n → ℝ) :
    ∑ j, fderiv ℝ (cofactorFn H i j) x (Pi.single j 1) = 0 := by
  set D2 := fderiv ℝ (fderiv ℝ H) x with hD2
  have hsym : ∀ v w, D2 v w = D2 w v :=
    (hH.contDiffAt (x := x)).isSymmSndFDerivAt (by simp; exact ENat.LEInfty.out)
  simp_rw [(hasFDerivAt_cofactorFn H hH i _ x).fderiv, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.linearDeriv_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = i
  · subst hk
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [killRow_apply_self, Function.update_idem]
    exact detCML.map_update_zero _ _
  · simp_rw [killRow_apply_ne hk]
    have := sum_det_symm_eq_zero (jacobian H x) (Ne.symm hk)
      (fun j l => D2 (Pi.single j 1) (Pi.single l 1) k)
      (fun j l => by simp only [hsym (Pi.single j 1)])
    exact this
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
