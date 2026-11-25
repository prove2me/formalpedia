-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.JMA.list_prod_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:35:13.975739+00:00
-- url     : https://prove2.me/submissions/b7d41234-27d6-40bc-9870-9b82caf64504

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PJmComm
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
open PositivityTheory.Rg.Cz.JMA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.JMA
theorem _root_.solution {A : Type} [Monoid A] (x : A) : ∀ (L : List A) (k : ℕ) (hk : k + 1 < L.length),
    (∀ t (ht : t < L.length), t ≠ k → t ≠ k + 1 → Commute L[t] x) → Commute (L[k] * L[k + 1]) x →
      Commute L.prod x
  | [], k, hk, _, _ => by simp at hk
  | [a], k, hk, _, _ => by simp at hk
  | a :: b :: L, 0, hk, h1, h2 => by
    rw [List.prod_cons, List.prod_cons, ← mul_assoc]
    refine h2.mul_left (Commute.list_prod_left _ _ fun y hy => ?_)
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hy
    exact h1 (t + 2) (by simp; omega) (by omega) (by omega)
  | a :: L, k + 1, hk, h1, h2 => by
    rw [List.prod_cons]
    exact (h1 0 (by simp) (by omega) (by omega)).mul_left (solution x L k (by simpa using hk)
      (fun t ht h h' => h1 (t + 1) (by simpa using ht) (by omega) (by omega)) h2)
end PositivityTheory.Rg.Cz.JMA
