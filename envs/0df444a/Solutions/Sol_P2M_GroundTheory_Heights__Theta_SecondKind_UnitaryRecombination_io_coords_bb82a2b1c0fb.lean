-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_io_coords_bb82a2b1c0fb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:16.880963+00:00
-- url     : https://prove2.me/submissions/24b92198-cc16-4b11-83ed-f41ab461cf35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_coords_io_58780eedfeee

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Theta.SecondKind
open GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
namespace GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
theorem _root_.solution (F : OrthoFrame) {X : MatProd F.p F.q} (hX : X ∈ lieProd F.p F.q) : F.io (coords F X) = X := by
  rw [← F.span, Submodule.mem_span_range_iff_exists_fun] at hX
  obtain ⟨c, rfl⟩ := hX
  have : (∑ i, c i • F.E i) = F.io c := rfl
  rw [this, coords_io]
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
