-- Prove2me | solution 1 for PI.OddDualWeyl.Low.hw_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:45.713914+00:00
-- url     : https://prove2.me/submissions/5eae2158-6192-4869-9b23-88ff62b817e8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.Low
variable {R : Type*} [CommRing R]
namespace PI.OddDualWeyl.Low
theorem _root_.solution {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : hw R hn ν ∈ weyl R r n hn ν :=
  Submodule.subset_span ⟨[], rfl⟩
end PI.OddDualWeyl.Low
