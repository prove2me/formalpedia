-- Prove2me | solution 1 for PI.BlockRatReal.UnitaryGroupMassFormula.Odd.map_genM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:59.637793+00:00
-- url     : https://prove2.me/submissions/bef50b9b-5c8f-41af-bcc9-a7e93dd5f523

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_EvenStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_Bridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_OddDualWeylFactorization
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_MapDetGenM
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.BlockRatReal PI.BlockRatReal.UnitaryGroupMassFormula PI.BlockRatReal.UnitaryGroupMassFormula.Odd
open PI.OddDualWeyl
namespace PI.BlockRatReal.UnitaryGroupMassFormula.Odd
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ) :
    (MvPolynomial.map φ).mapMatrix (genM R k) = genM S k := by
  ext i j; simp [genM]
end PI.BlockRatReal.UnitaryGroupMassFormula.Odd
