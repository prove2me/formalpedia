-- Prove2me | solution 1 for Scott1972.ContinuousLattice.theorem_2_12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:47:02.091989+00:00
-- url     : https://prove2.me/submissions/30d1f89c-b6a6-4491-ad04-a0918d0bd6dd

import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Theorems.Thm_Scott1972_ContinuousLattice_theorem_2_12_backward
import Theorems.Thm_IsInjectiveSpace_of_retract
import Theorems.Thm_Scott1972_ContinuousLattice_ScottMap_continuous
import Theorems.Thm_Scott1972_ContinuousLattice_theorem_2_12_forward


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
universe u
namespace Scott1972.ContinuousLattice
theorem _root_.solution {D : Type u} [TopologicalSpace D] [T0Space D] :
    IsInjectiveSpace.{u, u} D ↔
      ∃ (E : Type u) (inst : CompleteLattice E),
        @IsContinuousLattice E inst ∧
          Nonempty (@Homeomorph D E _ (@scottTopologicalSpace E inst)) := by
  refine ⟨theorem_2_12_backward, ?_⟩
  rintro ⟨E, inst, hE, ⟨h⟩⟩
  letI τE : TopologicalSpace E := @scottTopologicalSpace E inst
  exact @IsInjectiveSpace.of_retract E D τE _ (theorem_2_12_forward hE)
    ⟨⇑h, h.continuous⟩ ⟨⇑h.symm, h.symm.continuous⟩ (fun d => h.left_inv d)
end Scott1972.ContinuousLattice
