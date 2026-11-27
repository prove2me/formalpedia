-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Theta_orth_mem_fullChain_of_mem_49239274c101
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:13:56.115823+00:00
-- url     : https://prove2.me/submissions/15e61c6e-c47e-4222-82fb-f8c7182ef6a6

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
theorem _root_.solution {𝒲 : IsotropicFlag K H} {W : Submodule E (ι → E)}
    (hW : W ∈ 𝒲.members) : orth K H W ∈ fullChain 𝒲 :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hW)))
end GroundTheory.Heights₂.Theta
