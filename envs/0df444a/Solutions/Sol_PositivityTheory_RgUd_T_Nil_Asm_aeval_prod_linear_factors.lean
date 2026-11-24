-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Asm.aeval_prod_linear_factors
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:50.003193+00:00
-- url     : https://prove2.me/submissions/52e90063-11f6-4adc-bae0-aa6c0db43dcf

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_NilpotentHypotheses_AevalProdLinearFactors

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
theorem _root_.solution (R : Module.End ℂ M) (β : ℂ) (γ : ℝ → ℂ) (a : List ℝ) :
    aeval R ((a.map fun x => C β - C (γ x) * X).prod) =
      ((a.map fun x => β • LinearMap.id - γ x • R).prod : Module.End ℂ M) := by
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  show aeval R (C β - C (γ x) * X) = β • LinearMap.id - γ x • R
  rw [map_sub, map_mul, aeval_C, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul]
  rfl
end PositivityTheory.RgUd.T.Nil.Asm
