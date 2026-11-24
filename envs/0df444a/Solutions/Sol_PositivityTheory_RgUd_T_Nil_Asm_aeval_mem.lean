-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Asm.aeval_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:49.83484+00:00
-- url     : https://prove2.me/submissions/ccae4658-ba25-49cf-8c8a-d09c13d7fe3e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_NilpotentHypotheses_AevalProdLinearFactors
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Asm_pow_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Asm
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.RgUd.T.Nil.Asm
theorem _root_.solution (K : Submodule ℂ M) (R : Module.End ℂ M) (hK : ∀ m ∈ K, R m ∈ K) (p : ℂ[X]) :
    ∀ m ∈ K, (aeval R p) m ∈ K := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => intro m hm; rw [map_add, LinearMap.add_apply]; exact K.add_mem (hp m hm) (hq m hm)
  | monomial j a =>
    intro m hm
    rw [aeval_monomial, Module.End.mul_apply, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply]
    exact K.smul_mem _ (pow_mem K R hK j m hm)
end PositivityTheory.RgUd.T.Nil.Asm
