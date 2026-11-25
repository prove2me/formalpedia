-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CharacterRelations.part2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:46.889307+00:00
-- url     : https://prove2.me/submissions/974dd196-9ac1-46f3-ad2e-a04289626ffa

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepChar
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_eval_sumMono
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_vanish
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_add
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_mul
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_alg
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_uniq
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_qdet
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_gl
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_piJ_one
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_lift_alg
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
    (hE : GlRel E) (l : Fin n → ℂ) (hl : HasChar E l)
    (W : Submodule ℂ (TV n M (Fin 1))) (N : Type) [AddCommGroup N] [Module ℂ N] (F : Fin n → Fin n → Module.End ℂ N)
    (q : W →ₗ[ℂ] N) (hW : ∀ a b, ∀ w ∈ W, tE Finset.univ E a b w ∈ W) (hO : ∀ w ∈ W, Om E 0 w ∈ W) (k : Fin n)
    (hq : Function.Surjective q) (hqF : ∀ a b (w : W), q ⟨_, hW a b w w.2⟩ = F a b (q w))
    (hqO : ∀ w : W, q ⟨_, hO w w.2⟩ = l k • q w) : HasChar F (Function.update l k (l k + 1)) := by
  classical
  have hG := hT n M (Fin 1) E hE Finset.univ
  have hrelT : ∀ a b, Rel W q (tE Finset.univ E a b) (F a b) := fun a b w => ⟨hW a b w w.2, hqF a b w⟩
  have hrelO : Rel W q (Om E 0) (algebraMap ℂ (Module.End ℂ N) (l k)) := fun w =>
    ⟨hO w w.2, by rw [Module.algebraMap_end_apply]; exact hqO w⟩
  have hFG : GlRel F := rel_gl hq _ F hG.1 hrelT
  obtain ⟨c, hc⟩ := (hQ n N F hFG).2.1
  have key : ∀ u : ℂ, u ≠ -l k →
      qdet F u = algebraMap ℂ _ (∏ j, (u + Function.update l k (l k + 1) j)) := by
    intro u hu
    have hu' : u + l k ≠ 0 := fun h0 => hu (eq_neg_of_add_eq_zero_left h0)
    have hL := rel_mul (rel_add (rel_alg (W := W) (q := q) u) hrelO) (rel_qdet _ _ hrelT u)
    have e := hS n M E hE 1 u
    rw [piJ_one, piJ_one, hl u, lift_alg] at e
    rw [e] at hL
    have hR := rel_mul (rel_alg (W := W) (q := q) (∏ j, (u + l j)))
      (rel_add (rel_alg (W := W) (q := q) (u + 1)) hrelO)
    have h3 := rel_uniq hq hL hR
    rw [← map_add (algebraMap ℂ (Module.End ℂ N)), ← map_add (algebraMap ℂ (Module.End ℂ N)),
      ← map_mul (algebraMap ℂ (Module.End ℂ N))] at h3
    have hs : (∏ j, (u + l j)) * (u + 1 + l k) = (u + l k) * ∏ j, (u + Function.update l k (l k + 1) j) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
        Function.update_self]
      have hj : ∀ j ∈ Finset.univ.erase k, u + Function.update l k (l k + 1) j = u + l j := fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [Finset.prod_congr rfl hj]
      ring
    rw [hs, map_mul] at h3
    calc qdet F u = algebraMap ℂ (Module.End ℂ N) (u + l k)⁻¹ * (algebraMap ℂ _ (u + l k) * qdet F u) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hu', map_one, one_mul]
      _ = _ := by rw [h3, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hu', map_one, one_mul]
  have hD := vanish ((∑ i ∈ Finset.range (n + 1), monomial i (c i)) -
      (∏ j, (X + C (Function.update l k (l k + 1) j))).map (algebraMap ℂ (Module.End ℂ N))) (-l k) (by
    intro u hu
    rw [Polynomial.eval_sub, eval_sumMono, ← hc, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      Polynomial.eval_prod, key u hu]
    simp)
  intro u
  have e := congrArg (Polynomial.eval (algebraMap ℂ (Module.End ℂ N) u)) hD
  rw [Polynomial.eval_sub, eval_sumMono, ← hc, Polynomial.eval_map, Polynomial.eval₂_at_apply,
    Polynomial.eval_prod, Polynomial.eval_zero, sub_eq_zero] at e
  simpa using e
end PositivityTheory.Rg.Cz.CharacterRelations
