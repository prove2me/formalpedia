-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.HeightVanishing.Om_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:34:05.50581+00:00
-- url     : https://prove2.me/submissions/40c1c451-f7e6-4763-9ffd-2162381c821f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PHeight
import Theorems.Thm_PositivityTheory_Rg_Cz_Om_apply
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
theorem _root_.solution (p : P) (I : P → Fin n) (v : M) :
    Om E p (Pi.single I v : TV n M P) = ∑ c, Pi.single (Function.update I p c) (E (I p) c v) := by
  funext J
  rw [Om_apply, Finset.sum_apply]
  by_cases hJ : ∀ q, q ≠ p → J q = I q
  · rw [Finset.sum_eq_single_of_mem (I p) (Finset.mem_univ _) ?_,
      Finset.sum_eq_single_of_mem (J p) (Finset.mem_univ _) ?_]
    · have h1 : Function.update J p (I p) = I := by
        funext q; by_cases hq : q = p
        · subst hq; simp
        · rw [Function.update_of_ne hq]; exact hJ q hq
      have h2 : J = Function.update I p (J p) := by
        funext q; by_cases hq : q = p
        · subst hq; simp
        · rw [Function.update_of_ne hq]; exact hJ q hq
      rw [h1, Pi.single_eq_same, ← h2, Pi.single_eq_same]
    · intro c _ hc
      rw [Pi.single_eq_of_ne]
      intro h; apply hc; rw [h]; simp
    · intro a _ ha
      rw [Pi.single_eq_of_ne, map_zero]
      intro h; apply ha; rw [← h]; simp
  · push_neg at hJ
    obtain ⟨q, hq, hne⟩ := hJ
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro c _; rw [Pi.single_eq_of_ne]; intro h; apply hne; rw [h, Function.update_of_ne hq]
    · intro a _; rw [Pi.single_eq_of_ne, map_zero]; intro h; apply hne; rw [← h, Function.update_of_ne hq]
end PositivityTheory.Rg.Cz.HeightVanishing
