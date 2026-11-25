-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_evalCone_rename_blockIncl_0286f978dfe8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:39:39.139689+00:00
-- url     : https://prove2.me/submissions/ae1417b7-aa9f-4e70-9d3b-a6358e194785

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_VarsSubsetRangeBlockIncl

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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {F : Type*} [CommRing F] (k₀ : ι) (z : Cone n F)
    (f' : MvPolynomial (Coord (fun _ : Unit ↦ n k₀)) ℤ) :
    evalCone z (rename (blockIncl k₀) f') = evalCone (projBlock k₀ z) f' := by
  unfold evalCone
  rw [eval₂_rename]
  rfl
end GroundTheory.Heights₂.Heights
