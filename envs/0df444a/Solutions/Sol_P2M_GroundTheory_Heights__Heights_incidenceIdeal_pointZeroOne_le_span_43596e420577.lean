-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_incidenceIdeal_pointZeroOne_le_span_43596e420577
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:08.46067+00:00
-- url     : https://prove2.me/submissions/83fc739e-59df-4f14-8506-68136ffe3063

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_X_zero_one_dvd_sub_substZeroOne_0e2e6d7fe4f3

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    incIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1 ≤ Ideal.span {qLine} := by
  intro g hg
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hg
  rw [Ideal.mem_span_singleton, qLine]
  have hz : substZeroOne g = 0 := by
    apply MvPolynomial.map_injective (algebraMap ℚ (AlgebraicClosure ℚ)) (algebraMap ℚ _).injective
    rw [map_zero]
    apply MvPolynomial.funext
    intro v
    rw [eval_map, ← aeval_def, map_zero, substZeroOne, ← AlgHom.comp_apply, comp_aeval]
    have hw : (fun ij : Fin 1 × Fin 2 => aeval v (if ij = ((0 : Fin 1), (1 : Fin 2)) then (0 : MvPolynomial (Fin 1 × Fin 2) ℚ) else X ij)) ∈
        incidence (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1 := by
      refine ⟨![0, 1], fun h => one_ne_zero (congrFun h 1), fun g hg => ?_, fun i => ?_⟩
      · obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hg
        simp
      · obtain rfl : i = 0 := Subsingleton.elim _ _
        simp [Fin.sum_univ_two]
    exact hg _ hw
  simpa [hz] using X_zero_one_dvd_sub_substZeroOne g
end GroundTheory.Heights₂.Heights
