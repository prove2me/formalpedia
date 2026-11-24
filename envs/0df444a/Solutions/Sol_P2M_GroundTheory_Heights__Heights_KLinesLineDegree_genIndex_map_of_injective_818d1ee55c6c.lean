-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesLineDegree_genIndex_map_of_injective_818d1ee55c6c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:41.075998+00:00
-- url     : https://prove2.me/submissions/7681e775-f6b8-474e-8dae-b9547b18782c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesLineDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField Matrix
open scoped nonZeroDivisors
noncomputable section
open GroundTheory.Heights₂.Heights.KLinesLineDegree
variable {K : Type} [Field K] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.KLinesLineDegree
theorem _root_.solution {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G →+ G')
    (hf : Function.Injective f) (A B : AddSubgroup G) :
    genIndex (A.map f) (B.map f) = genIndex A B := by
  unfold genIndex
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hf,
    AddSubgroup.relIndex_map_map_of_injective _ _ hf]
end GroundTheory.Heights₂.Heights.KLinesLineDegree
