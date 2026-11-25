-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.HeightVanishing.pm_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:35:56.088269+00:00
-- url     : https://prove2.me/submissions/151d4fc8-090c-4dbd-b37a-94cebfefc154

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PHeight
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
open PositivityTheory.Rg.Cz.HeightVanishing
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable (E : Fin n → Fin n → Module.End ℂ M)
variable {P : Type} [Fintype P] [DecidableEq P]
namespace PositivityTheory.Rg.Cz.HeightVanishing
theorem _root_.solution (σ : Equiv.Perm P) (I : P → Fin n) (v : M) :
    pm σ (Pi.single I v : TV n M P) = Pi.single (I ∘ σ.symm) v := by
  funext J
  rw [pm_apply]
  simp only [Pi.single_apply, Equiv.eq_comp_symm]
end PositivityTheory.Rg.Cz.HeightVanishing
