-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Theta_mem_unipotentRadical_38b14c233376
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:13:47.70393+00:00
-- url     : https://prove2.me/submissions/e5e42beb-aa0e-40de-93e3-160a5c43e9b4

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
    g ∈ unipotentRadical H R 𝒲 ↔ ∀ B ∈ fullChain 𝒲, ∀ x ∈ extendScalars K R B,
      unitaryMat g *ᵥ x - x ∈ extendScalars K R (below (fullChain 𝒲) B) ∧
      unitaryMat g⁻¹ *ᵥ x - x ∈ extendScalars K R (below (fullChain 𝒲) B) :=
  Iff.rfl
end GroundTheory.Heights₂.Theta
