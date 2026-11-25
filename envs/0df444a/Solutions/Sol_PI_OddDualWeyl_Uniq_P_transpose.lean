-- Prove2me | solution 1 for PI.OddDualWeyl.Uniq.P_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:59:25.42818+00:00
-- url     : https://prove2.me/submissions/6f48a050-c890-4161-a83b-aa5fed9e95e5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Lemmata_GeneralBFactRightAlt_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightVectorUnique

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
open PI PI.OddDualWeyl PI.OddDualWeyl.Uniq
variable {Rg : Type*} [CommRing Rg] {k : ℕ}
namespace PI.OddDualWeyl.Uniq
theorem _root_.solution : (P Rg k)ᵀ = P Rg k := by
  ext i j
  simp only [P, Matrix.transpose_apply, Matrix.of_apply]
  congr 1
  exact propext ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
end PI.OddDualWeyl.Uniq
