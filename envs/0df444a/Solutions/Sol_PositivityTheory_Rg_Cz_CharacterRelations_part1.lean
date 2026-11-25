-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CharacterRelations.part1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:44:05.943617+00:00
-- url     : https://prove2.me/submissions/2f70604a-2809-4cc9-88f1-1b10ad7a79fa

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepChar
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_comm_alg
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_eval_mul_nc
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_eval_sumMono
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_vanish
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_prod_neg_zero
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_piJ_one
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_lift_alg
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_qdet_comm
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
open Formalism.REAL Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.CharacterRelations
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.CharacterRelations
theorem _root_.solution (hT : TensorGl) (hS : StepFormula) (hQ : QdetFacts) (E : Fin n → Fin n → Module.End ℂ M)
    (hE : GlRel E) (l : Fin n → ℂ) (hl : HasChar E l) :
    (List.ofFn fun k => Om E (0 : Fin 1) - algebraMap ℂ _ (l k)).prod = 0 := by
  classical
  have hG := hT n M (Fin 1) E hE Finset.univ
  obtain ⟨c, hc⟩ := (hQ n (TV n M (Fin 1)) (tE Finset.univ E) hG.1).2.1
  have hcomm : ∀ u, Commute (Om E (0 : Fin 1)) (qdet (tE Finset.univ E) u) := fun u =>
    qdet_comm _ _ (fun a b => hG.2.1 0 (Finset.mem_univ _) a b) u
  have hid : ∀ u : ℂ, qdet (tE Finset.univ E) u * (algebraMap ℂ (Module.End ℂ (TV n M (Fin 1))) u + Om E 0) =
      algebraMap ℂ _ (∏ k, (u + l k)) * (algebraMap ℂ _ u + (1 + Om E 0)) := by
    intro u
    have e := hS n M E hE 1 u
    rw [piJ_one, piJ_one, hl u, lift_alg] at e
    rw [← ((comm_alg _ u).symm.add_left (hcomm u)).eq, e, map_add, map_one, add_assoc]
  have hP : (∑ i ∈ Finset.range (n + 1), monomial i (c i)) * (X + C (Om E (0 : Fin 1))) -
      (∏ k, (X + C (l k))).map (algebraMap ℂ (Module.End ℂ (TV n M (Fin 1)))) * (X + C (1 + Om E 0)) = 0 := by
    apply vanish _ 0
    intro u _
    rw [Polynomial.eval_sub, eval_mul_nc _ _ _ (fun k => comm_alg _ _), eval_mul_nc _ _ _ (fun k => comm_alg _ _),
      eval_sumMono, ← hc, Polynomial.eval_map, Polynomial.eval₂_at_apply, Polynomial.eval_prod]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    rw [hid, sub_self]
  have hc' : ∀ a : Module.End ℂ (TV n M (Fin 1)), Commute a (Om E 0) →
      ∀ k, Commute ((X + C a).coeff k) (-Om E (0 : Fin 1)) := by
    intro a ha k
    rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
    refine Commute.add_left ?_ ?_ <;> split_ifs <;> simp [ha.neg_right]
  have e := congrArg (Polynomial.eval (-Om E (0 : Fin 1))) hP
  rw [Polynomial.eval_sub, eval_mul_nc _ _ _ (hc' _ (Commute.refl _)),
    eval_mul_nc _ _ _ (hc' _ ((Commute.one_left _).add_left (Commute.refl _))), Polynomial.eval_zero] at e
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at e
  rw [neg_add_cancel, mul_zero, zero_sub, show -Om E (0 : Fin 1) + (1 + Om E 0) = 1 by abel, mul_one,
    neg_eq_zero, Polynomial.eval_map, ← Polynomial.aeval_def, ← List.prod_ofFn, map_list_prod,
    List.map_ofFn] at e
  apply prod_neg_zero
  rw [List.map_ofFn]
  refine Eq.trans (congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))) e
  simp only [Function.comp_apply, map_add, Polynomial.aeval_X, Polynomial.aeval_C, neg_sub]
  abel
end PositivityTheory.Rg.Cz.CharacterRelations
