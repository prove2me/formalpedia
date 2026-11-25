-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_mem_fullChain_of_mem_07319cad7b47
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:54:12.930935+00:00
-- url     : https://prove2.me/submissions/8aecb621-29bf-424d-9ff3-a502d1f3cd0a

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
    (hW : W ∈ 𝒲.members) : W ∈ fullChain 𝒲 :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ hW))
end GroundTheory.Heights₂.Theta
