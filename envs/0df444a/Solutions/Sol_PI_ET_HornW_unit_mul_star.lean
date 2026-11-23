-- Prove2me | solution 1 for PI.ET.HornW.unit_mul_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:16.592926+00:00
-- url     : https://prove2.me/submissions/a5d4cc5c-7a78-40a4-ba4d-6335b151cd06

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
theorem _root_.solution {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ) :
    W * Wᴴ = 1 := by
  exact Unitary.mul_star_self_of_mem hW
end PI.ET.HornW
