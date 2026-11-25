-- Prove2me | solution 1 for PI.BlockRatReal.UnitaryGroupMassFormula.Odd.map_det_genM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:34:45.310399+00:00
-- url     : https://prove2.me/submissions/7bdd673e-722f-485c-a9a7-ca9add44492b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_EvenStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_Bridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_OddDualWeylFactorization
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_MapDetGenM
import Theorems.Thm_PI_BlockRatReal_UnitaryGroupMassFormula_Odd_map_genM
import Theorems.Thm_PI_OddDualWeyl_Uniq_map_genM


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
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ) :
    MvPolynomial.map φ (genM R k).det = (genM S k).det := by
  rw [RingHom.map_det, map_genM]
end PI.BlockRatReal.UnitaryGroupMassFormula.Odd
