-- Prove2me | solution 1 for PIW.AdelicOrbitU.hform_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:48:55.152097+00:00
-- url     : https://prove2.me/submissions/8c13ba15-8af4-4bdb-b267-1dd909888dd1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
import Theorems.Thm_PIW_AdelicOrbitU_hform_eq_dot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Matrix Formalism.UG
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)
namespace PIW.AdelicOrbitU
theorem _root_.solution (x y z : Fin n → S) :
    hform s J (x - y) z = hform s J x z - hform s J y z := by
  simp only [hform_eq_dot, dotProduct, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
end PIW.AdelicOrbitU
