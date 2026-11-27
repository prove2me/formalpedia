-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_toBase_mem_extendScalars_6d939e4090f3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:14:21.767505+00:00
-- url     : https://prove2.me/submissions/4202a100-48f9-426a-bb1e-07e62022bb08

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
variable (K) (R : Type*) [CommRing R] [Algebra K R]
variable {K R}
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution {W : Submodule E (ι → E)} {x : ι → E} (hx : x ∈ W) :
    toBase K R x ∈ extendScalars K R W :=
  Submodule.subset_span ⟨x, hx, rfl⟩
end GroundTheory.Heights₂.Theta
