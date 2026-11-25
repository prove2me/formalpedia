-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_le_orth_of_mem_4c827d4221dd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:49:59.423512+00:00
-- url     : https://prove2.me/submissions/b3940067-73a4-4d83-85c2-d02a12d26813

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Parabolic
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_orth_antitone_7a7d283f0c36
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_IsTotallyIsotropic_le_orth_45a92c67c747

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
theorem _root_.solution (𝒲 : IsotropicFlag K H) {W W' : Submodule E (ι → E)}
    (hW : W ∈ 𝒲.members) (hW' : W' ∈ 𝒲.members) : W ≤ orth K H W' := by
  rcases eq_or_ne W W' with rfl | hne
  · exact (𝒲.isotropic W hW).le_orth
  rcases 𝒲.isChain hW hW' hne with h | h
  · exact h.trans (𝒲.isotropic W' hW').le_orth
  · exact (𝒲.isotropic W hW).le_orth.trans (orth_antitone h)
end GroundTheory.Heights₂.Theta
