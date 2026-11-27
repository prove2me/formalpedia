-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_mem_parabolic_8c47d885937c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:13:29.900824+00:00
-- url     : https://prove2.me/submissions/5b641e51-b9c7-46cf-a7e5-bc111f79299d

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
variable (H : Matrix ι ι E)
variable (R : Type*) [CommRing R] [Algebra K R]
variable {H R}
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution {𝒲 : IsotropicFlag K H} {g : unitaryPoints K E H R} :
    g ∈ parabolic H R 𝒲 ↔ ∀ W ∈ 𝒲.members, ∀ x ∈ extendScalars K R W,
      unitaryMat g *ᵥ x ∈ extendScalars K R W ∧ unitaryMat g⁻¹ *ᵥ x ∈ extendScalars K R W :=
  Iff.rfl
end GroundTheory.Heights₂.Theta
