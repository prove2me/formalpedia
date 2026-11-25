-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_bddAbove_wittIndex_set_241dd391a18f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:22.520709+00:00
-- url     : https://prove2.me/submissions/e23c0d30-3091-42c0-b03f-18952e2a5af8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Parabolic

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
open Module Matrix TensorProduct GroundTheory.Automorphic NumberField
open scoped NumberField.AdeleRing
noncomputable section
set_option linter.unusedSectionVars false
open scoped Classical
variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (K) (H : Matrix ι ι E)
variable {K H}
variable (K H)
variable {K H}
variable (K H)
variable {K H}
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution :
    BddAbove {d | ∃ W : Submodule E (ι → E), IsTotallyIsotropic K H W ∧ finrank E W = d} := by
  refine ⟨Fintype.card ι, ?_⟩
  rintro d ⟨W, -, rfl⟩
  calc finrank E W ≤ finrank E (ι → E) := Submodule.finrank_le W
    _ = Fintype.card ι := Module.finrank_fintype_fun_eq_card E
end GroundTheory.Heights₂.Theta
