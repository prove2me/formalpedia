-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_not_isProper_of_isAnisotropic_5cf04831993b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:13:51.163148+00:00
-- url     : https://prove2.me/submissions/9664d654-c9c9-4790-a075-64206fb005b0

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
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (h : IsAnisotropic K H) (𝒲 : IsotropicFlag K H) :
    ¬ 𝒲.IsProper := by
  rintro ⟨W, hW, hne⟩
  apply hne
  rw [eq_bot_iff]
  intro x hx
  exact (Submodule.mem_bot E).2 (h x (𝒲.isotropic W hW x hx x hx))
end GroundTheory.Heights₂.Theta
