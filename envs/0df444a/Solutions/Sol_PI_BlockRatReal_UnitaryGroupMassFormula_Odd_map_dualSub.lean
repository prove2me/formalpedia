-- Prove2me | solution 1 for PI.BlockRatReal.UnitaryGroupMassFormula.Odd.map_dualSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:25.311807+00:00
-- url     : https://prove2.me/submissions/c5e6dc39-1c1e-45e2-8911-a253a77b5e15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_EvenStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_Bridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_OddDualWeylFactorization
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_MapDetGenM
import Theorems.Thm_PI_BlockRatReal_UnitaryGroupMassFormula_Odd_map_dualM
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
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ)
    (p : MvPolynomial (Fin k × Fin k) R) :
    MvPolynomial.map φ (dualSub R k p) = dualSub S k (MvPolynomial.map φ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [dualSub]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [dualSub, aeval_X]
    exact map_dualM φ k v.1 v.2
end PI.BlockRatReal.UnitaryGroupMassFormula.Odd
