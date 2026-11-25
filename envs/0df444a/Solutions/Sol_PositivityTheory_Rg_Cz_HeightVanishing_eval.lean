-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.HeightVanishing.eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:47:28.475065+00:00
-- url     : https://prove2.me/submissions/ed5b341a-2749-403d-a62f-694bc8a61ae0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PHeight
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_W_of
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_one_mem
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_letter_mem
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_mul_mem
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_Om_single
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_pm_single
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
theorem _root_.solution {d : ℕ} {g : Module.End ℂ (TV n M P)} (hg : Deg E d g) (J : P → Fin n) :
    ∀ I : P → Fin n, ∃ A ∈ W E d (H J I), ∀ v, g (Pi.single I v) J = A v := by
  induction hg with
  | one d =>
    intro I
    by_cases h : J = I
    · subst h; exact ⟨1, W_of E le_rfl (by simp [H]) (one_mem E d), fun v => by simp⟩
    · exact ⟨0, zero_mem _, fun v => by simp [Pi.single_eq_of_ne h]⟩
  | add _ _ ih1 ih2 =>
    intro I
    obtain ⟨A, hA, hAv⟩ := ih1 I
    obtain ⟨B, hB, hBv⟩ := ih2 I
    exact ⟨A + B, add_mem hA hB, fun v => by simp [hAv, hBv]⟩
  | smul c _ ih =>
    intro I
    obtain ⟨A, hA, hAv⟩ := ih I
    exact ⟨c • A, Submodule.smul_mem _ c hA, fun v => by simp [hAv]⟩
  | om p _ ih =>
    intro I
    choose A hA hAv using fun c => ih (Function.update I p c)
    refine ⟨∑ c, A c * E (I p) c, Submodule.sum_mem _ fun c _ => ?_, fun v => ?_⟩
    · refine W_of E le_rfl ?_ (mul_mem E (hA c) (letter_mem E (I p) c))
      have : H J (Function.update I p c) - H J I = ((I p : ℕ) : ℤ) - ((c : ℕ) : ℤ) := by
        simp only [H, ← Finset.sum_sub_distrib]
        rw [Finset.sum_eq_single p]
        · simp
        · intro q _ hq; simp [Function.update_of_ne hq]
        · simp
      linarith
    · rw [Module.End.mul_apply, Om_single, map_sum, Finset.sum_apply, LinearMap.sum_apply]
      exact Finset.sum_congr rfl fun c _ => by rw [hAv]; rfl
  | perm σ _ ih =>
    intro I
    obtain ⟨A, hA, hAv⟩ := ih (I ∘ σ.symm)
    refine ⟨A, W_of E le_rfl ?_ hA, fun v => ?_⟩
    · simp only [H, Finset.sum_sub_distrib, Function.comp_apply]
      rw [Equiv.sum_comp σ.symm (fun p => ((I p : ℕ) : ℤ))]
    · rw [Module.End.mul_apply, pm_single, hAv]
end PositivityTheory.Rg.Cz.HeightVanishing
