-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_latticeOf_neg_68559090b865
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:44:37.278516+00:00
-- url     : https://prove2.me/submissions/82049bb6-7878-4033-8dc0-8c1c15848755

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassReducedParamsNonemptyPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularGroup Complex NumberField
open scoped Real MatrixGroups nonZeroDivisors
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (t : ℂ) : latticeOf (-t) = latticeOf t := by
  unfold latticeOf
  congr 1
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.neg_mem _ (Submodule.subset_span (by simp))
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact Submodule.subset_span (by simp)
    · have : -(-x) ∈ Submodule.span ℤ ({1, -x} : Set ℂ) :=
        Submodule.neg_mem _ (Submodule.subset_span (by simp))
      simpa using this
end GroundTheory.Heights₂.Theta
