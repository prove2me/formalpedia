-- Prove2me | solution 1 for PI.WGB.rowAct_diag_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:19:57.463964+00:00
-- url     : https://prove2.me/submissions/08b1651e-d99d-4a2f-905b-f9b00c5d77be

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Theorems.Thm_PI_WGB_rowAct_diag_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGB
theorem _root_.solution {n N : ℕ} (t : Fin n → ℂ) (g : MvPolynomial (Fin N × Fin N) ℂ) (m : Fin n → ℕ)
    (hg : IsWeightedHomogeneous (wnB n N) g m) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N t)) g = chiB t m • g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [rowAct_diag_monomial, hg (mem_support_iff.mp he)]
end PI.WGB
