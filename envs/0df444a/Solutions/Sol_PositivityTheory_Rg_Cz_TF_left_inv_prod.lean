-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TF.left_inv_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:37:27.382803+00:00
-- url     : https://prove2.me/submissions/5cd8a46d-ce9e-4da3-b4a3-2f626f9f6a1e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinCK
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinA
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
open PositivityTheory.Rg.Cz.TF
namespace PositivityTheory.Rg.Cz.TF
theorem _root_.solution {A : Type*} [Ring A] (B : Subring A) :
    ∀ l : List A, (∀ a ∈ l, ∃ h ∈ B, h * a = 1) → ∃ h ∈ B, h * l.prod = 1 := by
  intro l
  induction l with
  | nil => intro _; exact ⟨1, B.one_mem, by simp⟩
  | cons a l ih =>
    intro hl
    obtain ⟨ha, hB, hae⟩ := hl a (List.mem_cons_self ..)
    obtain ⟨h, hB', he⟩ := ih fun b hb => hl b (List.mem_cons_of_mem _ hb)
    refine ⟨h * ha, B.mul_mem hB' hB, ?_⟩
    rw [List.prod_cons, mul_assoc, ← mul_assoc ha, hae, one_mul, he]
end PositivityTheory.Rg.Cz.TF
