-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryTripleAmplitude_eq_of_agree_on_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:05:13.154708+00:00
-- url     : https://prove2.me/submissions/9e0d44ef-3fa8-4b6b-a971-6f81c9944750

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTriples
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryPhysicalCCZ

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics
open scoped BigOperators
variable {J : Type} [Fintype J] [DecidableEq J]
omit [Fintype J] [DecidableEq J]
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (x : J × Fin 512)
    (a b : TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512))
    (h : ∀ v ∈ binaryTripleSupport J x, a v = b v) :
    binaryTripleAmplitude x a = binaryTripleAmplitude x b := by
  have hm (tag : ThreeCopyTag) : binaryTripleVertex J x tag ∈ binaryTripleSupport J x :=
    Finset.mem_map.mpr ⟨tag, Finset.mem_univ _, rfl⟩
  unfold binaryTripleAmplitude binaryTripleExponent
  rw [h _ (hm .first), h _ (hm .second), h _ (hm .third)]
end QEC.Distillation.Ngu24Binary
