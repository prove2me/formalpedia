-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TrOf.qdet_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:37:03.082456+00:00
-- url     : https://prove2.me/submissions/8fa302c7-8ce3-464f-8b07-01f0eddaf031

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransOf
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
open PositivityTheory.Rg.Cz.TrOf
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.TrOf
theorem _root_.solution {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B)
    (E : Fin n → Fin n → A) (u : ℂ) : φ (qdet E u) = qdet (fun a b => φ (E a b)) u := by
  simp only [qdet, qminor, Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Function.comp_def,
    map_add, apply_ite φ, map_zero, AlgHom.commutes]
end PositivityTheory.Rg.Cz.TrOf
