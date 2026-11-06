-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.localEmbedding_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:08:28.477042+00:00
-- url     : https://prove2.me/submissions/b7644f14-859f-4da8-aeba-0c9bf0efd391

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Core_Subsystem

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
open QEC.Semantics.FiniteSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.FiniteSubsystem
theorem _root_.solution (S : FiniteSubsystem ι) (h : S.selectedSystem) :
    S.localEmbedding h = h ⊗ₜ[Complex] S.complementAnchor :=
  rfl
end QEC.Semantics.FiniteSubsystem
