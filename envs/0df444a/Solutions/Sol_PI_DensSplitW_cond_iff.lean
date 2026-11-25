-- Prove2me | solution 1 for PI.DensSplitW.cond_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:38:17.648487+00:00
-- url     : https://prove2.me/submissions/7b559b1c-66a4-47f7-bfef-392b8bd63afc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_FiberCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_PhiXFinrankRange
import Theorems.Thm_PI_DensSplitW_phiX_apply

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
    (Gm : Matrix (Fin m) (Fin m) K) (X Y : Fin m → Fin n → K) :
    (∀ i j, ∑ k, ∑ l, X i k * Ph k l * Y j l = Gm i j) ↔ ∀ j, phiX Ph X (Y j) = Gm.transpose j := by
  constructor
  · intro h j
    funext i
    rw [phiX_apply, Matrix.transpose_apply]
    exact h i j
  · intro h i j
    have := congrFun (h j) i
    rwa [phiX_apply, Matrix.transpose_apply] at this
end PI.DensSplitW
