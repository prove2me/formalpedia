-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_IsotropicFlag_ofIsotropicVector_isProper_a11d6554aa1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:42:45.895255+00:00
-- url     : https://prove2.me/submissions/e1863250-017f-4bd6-8eaf-990c355820ec

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
open GroundTheory.Heights₂.Theta.IsotropicFlag
namespace GroundTheory.Heights₂.Theta.IsotropicFlag
theorem _root_.solution {x : ι → E} (hx : hermPair K H x x = 0) (hx0 : x ≠ 0) :
    (ofIsotropicVector hx).IsProper :=
  ⟨E ∙ x, Finset.mem_singleton_self _, by
    rwa [Ne, Submodule.span_singleton_eq_bot]⟩
end GroundTheory.Heights₂.Theta.IsotropicFlag
