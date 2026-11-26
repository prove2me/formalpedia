-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:27.165215+00:00
-- url     : https://prove2.me/submissions/455f0a5b-ec2d-4905-8db6-ab5a37159786

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_4_1_complete
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_ofNat
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem



set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    (∀ A : Set Pomega, A ⊆ Fixpoints f →
      gfpBelow f (⋂₀ A) ∈ Fixpoints (fun z => f z ∩ ⋂₀ A)) ∧
      ∀ {a} (_ha : IsRetract a),
        Fixpoints (funOf a) = {x | typed x a} := by
  constructor
  · intro A hA
    exact theorem_4_1_complete f hf A hA
  · intro a _ha
    ext x
    simp [Fixpoints, typed, eq_comm]
end Scott1976.DataTypesAsLattices
