-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12EvenFamily.distanceWitness_mem_evenCode_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:39:57.54625+00:00
-- url     : https://prove2.me/submissions/0c64823d-571e-457d-b183-161dea7a843a

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_distanceWitness_pair_even

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.Triorthogonal.BH12EvenFamily
theorem _root_.solution (q : Nat) :
    distanceWitness q ∈ (family q).evenCode.dual.carrier := by
  rw [LinearCode.mem_dual]
  intro y hy
  change y ∈ Submodule.span (ZMod 2) (Set.range (@evenWord q)) at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨r, rfl⟩
      exact distanceWitness_pair_even q r
  | zero => exact (wordPairing (distanceWitness q)).map_zero
  | add y z _ _ hy hz =>
      rw [(wordPairing (distanceWitness q)).map_add, hy, hz, add_zero]
  | smul c y _ hy =>
      rw [(wordPairing (distanceWitness q)).map_smul, hy, smul_zero]
end QEC.Distillation.Triorthogonal.BH12EvenFamily
