-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Cz_YoungTableau_colG_mul__a4fe529c9687
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:48:17.306556+00:00
-- url     : https://prove2.me/submissions/a1d5b99a-c77f-4bb5-8d20-6e0a15cdc9fd

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungB
import Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_mem_colG


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.YoungTableau
variable {n N : ℕ} {ι : Type} [DecidableEq ι] {C : Type} [DecidableEq C]
namespace PositivityTheory.Rg.Cz.YoungTableau
theorem _root_.solution {X : Type} [Fintype X] [DecidableEq X] {D : Type} [DecidableEq D] (col : X → D)
    {π π' : Equiv.Perm X} (h : π ∈ colG col) (h' : π' ∈ colG col) : π * π' ∈ colG col := (mem_colG col _).2 fun p => by
  rw [Equiv.Perm.mul_apply, (mem_colG col π).1 h, (mem_colG col π').1 h']
end PositivityTheory.Rg.Cz.YoungTableau
