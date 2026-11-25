-- Prove2me | solution 1 for PI.DensSplitW.phiX_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:34:58.685955+00:00
-- url     : https://prove2.me/submissions/b3a1ceed-8614-4c97-9ffc-155755dfaa07

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_FiberCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_PhiXFinrankRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.L2.SG.DensExact
open PI PI.DensSplitW
namespace PI.DensSplitW
theorem _root_.solution {K : Type} [Field K] {n m : ℕ} (Ph : Matrix (Fin n) (Fin n) K)
    (X : Fin m → Fin n → K) (y : Fin n → K) (i : Fin m) :
    phiX Ph X y i = ∑ k, ∑ l, X i k * Ph k l * y l := by
  simp only [phiX, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.of_apply]
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm
end PI.DensSplitW
