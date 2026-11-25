-- Prove2me | solution 1 for PIW.AdelicOrbitU.hform_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:48:57.863015+00:00
-- url     : https://prove2.me/submissions/4ed8f77f-d8c9-4a00-a65f-9a2d28241100

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
    hform s J x (y - z) = hform s J x y - hform s J x z := by
  simp only [hform_eq_dot, dotProduct, Matrix.mulVec_sub, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
end PIW.AdelicOrbitU
