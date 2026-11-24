-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_YPlusSec_newEmb_injective_b04c3e7a8d69
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:54.999881+00:00
-- url     : https://prove2.me/submissions/a8c1b5e8-eeb8-4f4f-a7c8-e3088f51a005

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSec

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.YPlusSec
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.YPlusSec
theorem _root_.solution : Function.Injective (newEmb D) := by
  rintro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h
  exact congrArg (Sigma.mk ()) (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
end GroundTheory.Heights₂.Heights.YPlusSec
