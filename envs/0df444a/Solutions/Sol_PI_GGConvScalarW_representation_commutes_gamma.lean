-- Prove2me | solution 1 for PI.GGConvScalarW.representation_commutes_gamma
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:00.342797+00:00
-- url     : https://prove2.me/submissions/7252bd7e-0106-4b9b-8db0-2484c7297112

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_CardUNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_Reindex
import Theorems.Thm_PI_GGConvScalarW_gam_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic Finset
namespace PI.GGConvScalarW
theorem _root_.solution : RepGamComm := by
  intro F _ _ k ψ₀ V _ _ π g
  apply LinearMap.ext
  intro v
  simp only [repGam, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul]
  have hm : ∀ a b : GL (Fin k) F, π a (π b v) = π (a * b) v := fun a b => by
    rw [map_mul, Module.End.mul_apply]
  simp only [hm]

  rw [← Equiv.sum_comp (MulAut.conj g).toEquiv (fun x => gam ψ₀ x • π (x * g) v)]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  rw [gam_conj]
  congr 2
  group
end PI.GGConvScalarW
