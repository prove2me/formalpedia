-- Prove2me | solution 1 for PI.LocLatSat.UnitaryGroupMassFormula.bcG_smulR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:36.05511+00:00
-- url     : https://prove2.me/submissions/49a66966-4f34-4f96-bfdb-f68fe9946388

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
theorem _root_.solution (r : R) (x : Fin n → K) : bcG φ (r • x) = φ (algebraMap R K r) • bcG φ x := by
  funext i
  simp [bcG, Algebra.smul_def, map_mul]
end PI.LocLatSat.UnitaryGroupMassFormula
