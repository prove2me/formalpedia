-- Prove2me | solution 1 for PI.KLW.Ind.hf_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:51:52.564875+00:00
-- url     : https://prove2.me/submissions/ce6af82f-f8e6-4bd3-ab7c-b10743284a08

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOneInduction
import Theorems.Thm_PI_KLW_Ind_extL_self
import Theorems.Thm_PI_KLW_Ind_hf_ext_ext
import Theorems.Thm_PI_KLW_Ind_hf_add_left
import Theorems.Thm_PI_KLW_Ind_hf_add_right
import Theorems.Thm_PI_KLW_Ind_hf_single_left
import Theorems.Thm_PI_KLW_Ind_hf_smul_left
import Theorems.Thm_PI_KLW_Ind_hf_smul_right


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
    (i0 : ι) (a b : {i // i ≠ i0} → K) (x y : K) :
    hf c (extL i0 a + x • Pi.single i0 1) (extL i0 b + y • Pi.single i0 1)
      = hf c a b + x * c y := by
  simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, hf_ext_ext,
    hf_single_right, hf_single_left, extL_self, map_zero, Pi.add_apply, Pi.smul_apply,
    Pi.single_eq_same, smul_eq_mul, mul_one, zero_add]
  ring
end PI.KLW.Ind
