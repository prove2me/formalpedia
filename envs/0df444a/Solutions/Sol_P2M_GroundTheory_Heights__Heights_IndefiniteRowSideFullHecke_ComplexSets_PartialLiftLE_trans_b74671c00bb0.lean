-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PartialLiftLE_trans_b74671c00bb0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:11.226783+00:00
-- url     : https://prove2.me/submissions/c2c678c8-6179-44e7-bb5c-ae6379f136a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothFrobeniusLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothPartialLifts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Polynomial IntermediateField
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
variable {F K B : Type*} [Field F] [Field K] [Algebra F K] [CommRing B] [Algebra F B]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace PartialLiftLE
theorem _root_.solution {a b d : Σ L : IntermediateField F K, L →ₐ[F] B} (h₁ : PartialLiftLE a b)
    (h₂ : PartialLiftLE b d) : PartialLiftLE a d := by
  obtain ⟨h₁, h₁'⟩ := h₁
  obtain ⟨h₂, h₂'⟩ := h₂
  exact ⟨h₁.trans h₂, fun y => by rw [← h₁' y, ← h₂' (IntermediateField.inclusion h₁ y)]; rfl⟩
end PartialLiftLE
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
