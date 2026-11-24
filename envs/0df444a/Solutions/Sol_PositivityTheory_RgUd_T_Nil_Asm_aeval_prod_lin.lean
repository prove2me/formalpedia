-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Asm.aeval_prod_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:03.612216+00:00
-- url     : https://prove2.me/submissions/67c8aae3-549c-4860-b697-3385f3bc4a8a

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
theorem _root_.solution (R : Module.End ℂ M) (α : ℝ → ℂ) (a : List ℝ) :
    aeval R ((a.map fun x => X - C (α x)).prod) = ((a.map fun x => R - α x • LinearMap.id).prod : Module.End ℂ M) := by
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp [Algebra.algebraMap_eq_smul_one, Module.End.one_eq_id]
end PositivityTheory.RgUd.T.Nil.Asm
