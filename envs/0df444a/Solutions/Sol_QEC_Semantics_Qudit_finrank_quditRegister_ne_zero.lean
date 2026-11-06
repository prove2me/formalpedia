-- Prove2me | solution 1 for QEC.Semantics.Qudit.finrank_quditRegister_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:44:45.270138+00:00
-- url     : https://prove2.me/submissions/b6249b2a-b929-483d-a77b-7393680db50c

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.Qudit
namespace QEC.Semantics.Qudit
theorem _root_.solution {ι : Type u} [Fintype ι]
    (q : ι → Nat) (hq : ∀ i, 0 < q i) :
    (Module.finrank Complex (QuditRegister q) : Complex) ≠ 0 := by
  letI : Nonempty (Label q) := label_nonempty q hq
  rw [finrank_euclideanSpace]
  exact_mod_cast Nat.ne_of_gt Fintype.card_pos
end QEC.Semantics.Qudit
