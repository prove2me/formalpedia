-- Prove2me | solution 1 for PI.ET.HornW.anti_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:57.970279+00:00
-- url     : https://prove2.me/submissions/7816679b-b685-4f18-ad5b-441ed93ba67b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_NormDetConjExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped MatrixOrder ComplexOrder
noncomputable section
open PI PI.ET
open PI.ET.HornW
variable {n : ℕ}
namespace PI.ET.HornW
theorem _root_.solution {d : Fin n → ℝ} (hd : Antitone d) : Antitone (fun i => Real.exp (2 * d i)) :=
  fun i j hij => Real.exp_le_exp.mpr (by have := hd hij; linarith)
end PI.ET.HornW
