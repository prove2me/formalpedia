-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TA.glRel_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:37:30.442206+00:00
-- url     : https://prove2.me/submissions/781d5254-e783-46a9-ad7c-6ef39a903423

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
    (E : Fin m → Fin m → A) (h : GlRel E) : GlRel fun a b => φ (E a b) := by
  intro a b c d
  dsimp only
  rw [← map_mul, ← map_mul, ← map_sub, h a b c d]
  split_ifs <;> simp
end PositivityTheory.Rg.Cz.TA
