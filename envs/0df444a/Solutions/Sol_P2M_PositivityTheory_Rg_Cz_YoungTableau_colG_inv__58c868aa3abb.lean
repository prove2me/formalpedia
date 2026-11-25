-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Cz_YoungTableau_colG_inv__58c868aa3abb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:55:30.861325+00:00
-- url     : https://prove2.me/submissions/d1e036f3-45d6-4817-b3d0-9aa34bebc3a3

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungB
import Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_mem_colG
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.YoungTableau
variable {n N : ℕ} {ι : Type} [DecidableEq ι] {C : Type} [DecidableEq C]
namespace PositivityTheory.Rg.Cz.YoungTableau
theorem _root_.solution {X : Type} [Fintype X] [DecidableEq X] {D : Type} [DecidableEq D] (col : X → D)
    {π : Equiv.Perm X} (h : π ∈ colG col) : π⁻¹ ∈ colG col := (mem_colG col _).2 fun p => by
  have hp := (mem_colG col π).1 h (π⁻¹ p)
  simp at hp
  exact hp.symm
end PositivityTheory.Rg.Cz.YoungTableau
