-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12EvenFamily.distanceWitness_pair_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:37:44.663547+00:00
-- url     : https://prove2.me/submissions/2756fbd5-ae44-414f-8ea4-2327302ad93d

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
theorem _root_.solution {q : Nat} (a : OddRow q) :
    wordPairing (distanceWitness q) (oddWord a) = 1 := by
  classical
  rw [distanceWitness, wordPairing.map_add]
  change wordPairing (Pi.single (Sum.inl (0 : Fin 4)) 1) (oddWord a) +
      wordPairing (Pi.single (Sum.inr (Sum.inl (0 : Fin 4))) 1) (oddWord a) = 1
  rw [wordPairing_single_one, wordPairing_single_one]
  rfl
end QEC.Distillation.Triorthogonal.BH12EvenFamily
