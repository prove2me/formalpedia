-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.WallAlgP.eigen_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:37:10.648237+00:00
-- url     : https://prove2.me/submissions/4b6a5b4b-df18-4960-8a8a-bf135d436f01

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PWallAlgA
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
open PositivityTheory.Rg.Cz.WallAlgP
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.WallAlgP
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) (μ : ℕ → ℂ) (L : List ℕ)
    (hL : (L.map fun r => T - algebraMap ℂ _ (μ r)).prod = 0) (z : V) (hz : z ≠ 0) (lam : ℂ) (h : T z = lam • z) :
    ∃ r : ℕ, lam = μ r := by
  have h2 : ∀ L : List ℕ, (L.map fun r => T - algebraMap ℂ _ (μ r)).prod z = (L.map fun r => lam - μ r).prod • z := by
    intro L
    induction L with
    | nil => simp
    | cons r L ih =>
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, h,
        Module.algebraMap_end_apply, ← sub_smul, smul_smul, List.map_cons, List.prod_cons, mul_comm]
  have h3 := h2 L
  rw [hL, LinearMap.zero_apply] at h3
  have h4 := (smul_eq_zero.mp h3.symm).resolve_right hz
  obtain ⟨r, -, hr⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h4)
  exact ⟨r, sub_eq_zero.mp hr⟩
end PositivityTheory.Rg.Cz.WallAlgP
