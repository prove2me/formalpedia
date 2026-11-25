-- Prove2me | solution 1 for PI.DensSplitW.phiX_finrank_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:35:03.077274+00:00
-- url     : https://prove2.me/submissions/efa8ded7-6082-4c04-bed8-3474b3bb43ec

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_FiberCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_PhiXFinrankRange
import Theorems.Thm_PI_DensSplitW_phiX_finrank_range

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
    (hPh : IsUnit Ph.det) (X : Fin m → Fin n → K) (hX : LinearIndependent K X) :
    Module.finrank K (LinearMap.ker (phiX Ph X)) = n - m := by
  have h := LinearMap.finrank_range_add_finrank_ker (phiX Ph X)
  rw [phiX_finrank_range Ph hPh X hX, Module.finrank_fin_fun] at h
  omega
end PI.DensSplitW
