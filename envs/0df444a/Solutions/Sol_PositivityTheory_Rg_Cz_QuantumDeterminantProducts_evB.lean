-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QuantumDeterminantProducts.evB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:38.175301+00:00
-- url     : https://prove2.me/submissions/0adcb6e4-c88e-4f56-a959-4bf778c90be4

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PPiQdet
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
open PositivityTheory.Rg.Cz.QuantumDeterminantProducts
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.QuantumDeterminantProducts
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (h : TV n M (Fin n)) (l : List (Fin n)) (hl : l.Nodup)
    (I : Fin n → Fin n) :
    ev E u l I h = ∑ c ∈ Finset.univ.filter (fun c : Fin n → Fin n => ∀ p, p ∉ l → c p = I p),
      (l.map fun k : Fin n => Tm E (u - (k : ℂ)) (c k) (I k)).prod (h c) := by
  induction l generalizing I with
  | nil =>
    rw [Finset.sum_eq_single I]
    · simp [ev]
    · intro c hc hne
      exfalso
      apply hne
      funext p
      exact (Finset.mem_filter.mp hc).2 p (by simp)
    · intro hI
      exfalso
      apply hI
      simp
  | cons k l ih =>
    have hk : k ∉ l := (List.nodup_cons.mp hl).1
    have hl' := (List.nodup_cons.mp hl).2
    simp only [ev, ih hl']
    conv_rhs => rw [← Finset.sum_fiberwise _ (fun c : Fin n → Fin n => c k)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr ?_ fun c hc => ?_
    · ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons, not_or]
      constructor
      · intro H
        refine ⟨fun p hp => ?_, ?_⟩
        · rw [H p hp.2, Function.update_of_ne hp.1]
        · rw [H k hk, Function.update_self]
      · rintro ⟨H, hca⟩ p hp
        by_cases hpk : p = k
        · subst hpk
          rw [hca, Function.update_self]
        · rw [H p ⟨hpk, hp⟩, Function.update_of_ne hpk]
    · simp only [Finset.mem_filter] at hc
      have hca : c k = a := hc.2
      have hm : l.map (fun k' : Fin n => Tm E (u - (k' : ℂ)) (c k') (Function.update I k a k'))
          = l.map (fun k' : Fin n => Tm E (u - (k' : ℂ)) (c k') (I k')) := by
        apply List.map_congr_left
        intro x hx
        have hxk : x ≠ k := by
          rintro rfl
          exact hk hx
        rw [Function.update_of_ne hxk]
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, hca, hm]
end PositivityTheory.Rg.Cz.QuantumDeterminantProducts
