-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.LieInverse.Sop_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:43:53.309931+00:00
-- url     : https://prove2.me/submissions/e0907915-c41c-4b66-be82-d8fbd1319896

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PLieInv
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
open PositivityTheory.Rg.Cz.LieInverse
namespace PositivityTheory.Rg.Cz.LieInverse
theorem _root_.solution {ι : Type} {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (E : ι → Fin n → Fin n → Module.End ℂ M)
    (bar : ι → ι) (τ : ι) (X Y : Matrix (Fin n) (Fin n) ℂ) : Sop E bar τ (X + Y) = Sop E bar τ X + Sop E bar τ Y := by
  simp only [Sop, Matrix.add_apply, add_smul, star_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by abel
end PositivityTheory.Rg.Cz.LieInverse
