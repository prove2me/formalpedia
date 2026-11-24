-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Cz_TA_qdet_map__2871d26b2e36
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:38.430059+00:00
-- url     : https://prove2.me/submissions/31752f74-1db1-479d-a19b-f9d24c0fdfd0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllA
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.TA
theorem _root_.solution {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {m : ℕ} (φ : A →ₐ[ℂ] B)
    (E : Fin m → Fin m → A) (u : ℂ) : φ (qdet E u) = qdet (fun a b => φ (E a b)) u := by
  simp [qdet, qminor, Tm, map_list_prod, List.map_ofFn, Function.comp_def, apply_ite φ]
end PositivityTheory.Rg.Cz.TA
