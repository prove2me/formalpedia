-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.HeightVanishing.mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:39.401345+00:00
-- url     : https://prove2.me/submissions/ad24c2e7-0949-499a-b4e2-a3c878fb11eb

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PHeight
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_word_mem
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_W_ind
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
theorem _root_.solution {k k' : ℕ} {h h' : ℤ} {A B : Module.End ℂ M} (hA : A ∈ W E k h) (hB : B ∈ W E k' h') :
    A * B ∈ W E (k + k') (h + h') := by
  have key : ∀ w w' : List (Fin n × Fin n), w.length ≤ k → ht w = h → w'.length ≤ k' → ht w' = h' →
      word E w * word E w' ∈ W E (k + k') (h + h') := by
    intro w w' h1 h2 h3 h4
    have e : word E w * word E w' = word E (w ++ w') := by simp [word, List.prod_append]
    rw [e]
    refine word_mem E _ (by simp only [List.length_append]; omega) ?_
    rw [← h2, ← h4]; simp [ht, List.sum_append]
  refine W_ind E (p := fun A => A * B ∈ W E (k + k') (h + h')) (by simp)
    (fun x y hx hy => by rw [add_mul]; exact add_mem hx hy)
    (fun c x hx => by rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx) ?_ hA
  intro w h1 h2
  refine W_ind E (p := fun B => word E w * B ∈ W E (k + k') (h + h')) (by simp)
    (fun x y hx hy => by rw [mul_add]; exact add_mem hx hy)
    (fun c x hx => by rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx) ?_ hB
  intro w' h3 h4
  exact key w w' h1 h2 h3 h4
end PositivityTheory.Rg.Cz.HeightVanishing
