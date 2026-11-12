-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12EvenFamily.distanceWitness_not_mem_rowCode_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:39:39.504943+00:00
-- url     : https://prove2.me/submissions/2e0ff25d-9b4f-4c60-96b8-2c7226f9b873

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_distanceWitness_pair_odd

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.Triorthogonal.BH12EvenFamily
theorem _root_.solution {q : Nat} (hq : 0 < q) :
    distanceWitness q ∉ (family q).rowCode.dual.carrier := by
  intro hmem
  let a : OddRow q := (⟨0, hq⟩, 0)
  have hpair := (family q).rowCode.orthogonal_of_mem_dual hmem
    ((family q).row_mem_rowCode (Sum.inl a))
  change wordPairing (distanceWitness q) (oddWord a) = 0 at hpair
  rw [distanceWitness_pair_odd] at hpair
  exact one_ne_zero hpair
end QEC.Distillation.Triorthogonal.BH12EvenFamily
