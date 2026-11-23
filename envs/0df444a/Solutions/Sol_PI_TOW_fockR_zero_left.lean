-- Prove2me | solution 1 for PI.TOW.fockR_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:40.108982+00:00
-- url     : https://prove2.me/submissions/28622f59-fba5-48ac-bc10-232e656cba5b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW
open PI.TO
variable {σ R : Type*} [CommRing R]
namespace PI.TOW
theorem _root_.solution (g : MvPolynomial σ R) : fockR 0 g = 0 := by
  simp [fockR]
end PI.TOW
