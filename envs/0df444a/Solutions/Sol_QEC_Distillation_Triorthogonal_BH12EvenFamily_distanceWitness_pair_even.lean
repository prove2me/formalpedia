-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12EvenFamily.distanceWitness_pair_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:37:11.109892+00:00
-- url     : https://prove2.me/submissions/a3b845c0-f481-4652-a43b-137da3929793

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
section
noncomputable section
namespace QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
private theorem wordPairing_single_one {q : Nat} (j : Column q)
    (x : Word (ZMod 2) (Column q)) :
    wordPairing (Pi.single j 1) x = x j := by
  classical
  rw [wordPairing_apply, single_one_dotProduct]
end QEC.Distillation.Triorthogonal.BH12EvenFamily
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.Triorthogonal.BH12EvenFamily
theorem _root_.solution (q : Nat) (r : EvenRow) :
    wordPairing (distanceWitness q) (evenWord r) = 0 := by
  classical
  rw [distanceWitness, wordPairing.map_add]
  change wordPairing (Pi.single (Sum.inl (0 : Fin 4)) 1) (evenWord r) +
      wordPairing (Pi.single (Sum.inr (Sum.inl (0 : Fin 4))) 1) (evenWord r) = 0
  rw [wordPairing_single_one, wordPairing_single_one]
  change evenFourBlock r 0 + evenFourBlock r 0 = 0
  exact ZModModule.add_self _
end QEC.Distillation.Triorthogonal.BH12EvenFamily
