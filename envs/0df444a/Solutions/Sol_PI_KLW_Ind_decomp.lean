-- Prove2me | solution 1 for PI.KLW.Ind.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:55:13.4389+00:00
-- url     : https://prove2.me/submissions/d63a8878-44c1-4208-80c9-cde33c86f12d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOneInduction
import Theorems.Thm_PI_KLW_Ind_extL_self
import Theorems.Thm_PI_KLW_Ind_extL_ne
import Theorems.Thm_PI_KLW_Ind_resL_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.Ind
open PI.KLW
namespace PI.KLW.Ind
theorem _root_.solution {K : Type} [Field K] {ι : Type} [DecidableEq ι] (i0 : ι) (v : ι → K) :
    v = extL i0 (resL i0 v) + v i0 • Pi.single i0 1 := by
  funext i
  by_cases h : i = i0
  · subst h
    simp [extL_self]
  · have := extL_ne i0 (resL i0 v) ⟨i, h⟩
    simp only at this
    simp [this, resL_apply, Pi.single_eq_of_ne h]
end PI.KLW.Ind
