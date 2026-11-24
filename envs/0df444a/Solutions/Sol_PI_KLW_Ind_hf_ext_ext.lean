-- Prove2me | solution 1 for PI.KLW.Ind.hf_ext_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:07:26.347927+00:00
-- url     : https://prove2.me/submissions/c60bb9f8-afcd-48b9-86f1-8b98c01a907f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOneInduction
import Theorems.Thm_PI_KLW_Ind_extL_self
import Theorems.Thm_PI_KLW_Ind_extL_ne

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
theorem _root_.solution {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (i0 : ι) (a b : {i // i ≠ i0} → K) : hf c (extL i0 a) (extL i0 b) = hf c a b := by
  unfold hf
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i0]
  simp only [extL_self, extL_ne, zero_mul, zero_add]
end PI.KLW.Ind
