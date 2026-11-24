-- Prove2me | solution 1 for PI.KLW.NO.coprime_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:46:14.505055+00:00
-- url     : https://prove2.me/submissions/c2c0ae06-5cb2-45dc-b3f8-536e0592f9c6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.NO
variable {K : Type} [Field K] [NumberField K] {p : ℕ}
namespace PI.KLW.NO
theorem _root_.solution (hp : p.Prime) {s : ℕ} (hs : Nat.Coprime s p) : s ≠ 0 := by
  rintro rfl
  exact hp.ne_one (by simpa using hs)
end PI.KLW.NO
