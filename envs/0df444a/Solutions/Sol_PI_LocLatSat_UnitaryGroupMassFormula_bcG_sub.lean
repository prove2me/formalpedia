-- Prove2me | solution 1 for PI.LocLatSat.UnitaryGroupMassFormula.bcG_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:40.870935+00:00
-- url     : https://prove2.me/submissions/23ddfce9-01db-4ff0-a525-c5143a0c0f81

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeSaturation_BcGSmulR
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open scoped nonZeroDivisors
open PI PI.LocLatSat PI.LocLatSat.UnitaryGroupMassFormula
variable {R K S : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] (φ : K →+* S) (O : Subring S) {n : ℕ}
omit [IsDedekindDomain R] [IsFractionRing R K]
namespace PI.LocLatSat.UnitaryGroupMassFormula
theorem _root_.solution (x y : Fin n → K) : bcG φ (x - y) = bcG φ x - bcG φ y := by
  funext i
  simp [bcG, map_sub]
end PI.LocLatSat.UnitaryGroupMassFormula
