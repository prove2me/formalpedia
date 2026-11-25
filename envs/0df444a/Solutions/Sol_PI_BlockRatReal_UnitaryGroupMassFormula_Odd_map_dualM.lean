-- Prove2me | solution 1 for PI.BlockRatReal.UnitaryGroupMassFormula.Odd.map_dualM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:34:49.361175+00:00
-- url     : https://prove2.me/submissions/15c5ab66-7972-4292-b80d-c3a4f92f6538

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_EvenStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_Bridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_OddDualWeylFactorization
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_MapDetGenM
import Theorems.Thm_PI_BlockRatReal_UnitaryGroupMassFormula_Odd_map_genM
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_PI_OddDualWeyl_Uniq_map_genM
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
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ) (i j : Fin k) :
    MvPolynomial.map φ (dualM R k i j) = dualM S k i j := by
  have h := congrFun (congrFun (RingHom.map_adjugate (MvPolynomial.map φ) (genM R k)) (Fin.rev j)) i
  rw [map_genM] at h
  simpa [dualM, RingHom.mapMatrix_apply, Matrix.map_apply] using h
end PI.BlockRatReal.UnitaryGroupMassFormula.Odd
