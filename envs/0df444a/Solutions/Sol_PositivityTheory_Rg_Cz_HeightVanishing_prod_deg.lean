-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.HeightVanishing.prod_deg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:53:24.213887+00:00
-- url     : https://prove2.me/submissions/373d62b8-d14b-4ded-a57c-d002be48b78a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PHeight
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_deg_succ
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
namespace PositivityTheory.Rg.Cz.HeightVanishing
theorem _root_.solution (L : List ℂ) :
    Deg E L.length (L.map fun r => Om E (0 : Fin 1) - algebraMap ℂ _ r).prod ∧
      Commute (Om E (0 : Fin 1)) (L.map fun r => Om E (0 : Fin 1) - algebraMap ℂ _ r).prod := by
  induction L with
  | nil => exact ⟨Deg.one 0, Commute.one_right _⟩
  | cons r L ih =>
    obtain ⟨h1, h2⟩ := ih
    have hc : Commute (Om E (0 : Fin 1)) (Om E 0 - algebraMap ℂ _ r) :=
      (Commute.refl _).sub_right (show Commute (algebraMap ℂ _ r) (Om E (0 : Fin 1)) from Algebra.commutes r _).symm
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    refine ⟨?_, hc.mul_right h2⟩
    rw [sub_mul, h2.eq, ← Algebra.smul_def, sub_eq_add_neg, ← neg_smul]
    exact Deg.add (Deg.om 0 h1) (Deg.smul (-r) (deg_succ E h1))
end PositivityTheory.Rg.Cz.HeightVanishing
