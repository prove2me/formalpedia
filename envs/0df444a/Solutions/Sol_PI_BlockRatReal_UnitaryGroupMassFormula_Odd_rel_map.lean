-- Prove2me | solution 1 for PI.BlockRatReal.UnitaryGroupMassFormula.Odd.rel_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:45:49.930592+00:00
-- url     : https://prove2.me/submissions/cecf0451-0e9c-443e-b443-7719a9069ca5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_EvenStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_Bridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_OddDualWeylFactorization
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_MapDetGenM
import Theorems.Thm_PI_BlockRatReal_UnitaryGroupMassFormula_Odd_map_det_genM
import Theorems.Thm_PI_BlockRatReal_UnitaryGroupMassFormula_Odd_map_dualSub
import Theorems.Thm_PI_OddDualWeyl_Red_map_det_genM
import Theorems.Thm_PI_OddDualWeyl_Red_map_dualSub


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
open PI PI.BlockRatReal PI.BlockRatReal.UnitaryGroupMassFormula PI.BlockRatReal.UnitaryGroupMassFormula.Odd
open PI.OddDualWeyl
namespace PI.BlockRatReal.UnitaryGroupMassFormula.Odd
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (k M : ℕ)
    (f f' : MvPolynomial (Fin k × Fin k) R) (h : PI.OddDualWeyl.Rel R k M f f') :
    PI.OddDualWeyl.Rel S k M (MvPolynomial.map φ f) (MvPolynomial.map φ f') := by
  unfold PI.OddDualWeyl.Rel at *
  rw [← map_dualSub, h, map_mul, map_pow, map_det_genM]
end PI.BlockRatReal.UnitaryGroupMassFormula.Odd
