-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.stepFormula_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:15.549561+00:00
-- url     : https://prove2.me/submissions/5263646b-2ef0-4fde-96c1-354672f767ce

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepFormulaA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepFormula
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_one
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_conj_eq
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_liftA_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_lift_PiJ
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_qdet_map
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_mul
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
open PStepFormula
namespace PositivityTheory.Rg.Cz
theorem _root_.solution : TensorGl → JMComm → PiQdet → Curry → StepFormula := by
  intro hT hJ hQ hC n M _ _ E hE m
  induction m generalizing M with
  | zero =>
    intro u
    have h0 : (tE (Finset.univ : Finset (Fin 0)) E : Fin n → Fin n → Module.End ℂ (TV n M (Fin 0))) =
        fun a b => liftA n M (Fin 0) (E a b) := by
      funext a b; simp [tE, liftA_apply]
    rw [h0, ← qdet_map, liftA_apply]
    simp [PiJ]
  | succ m ih =>
    intro u
    obtain ⟨hbij, h2, h3, h4, h5, -, -⟩ := hC n M E m 1
    set e := LinearEquiv.ofBijective (curF n M m 1) hbij
    have hG : GlRel (tE (Finset.univ : Finset (Fin m)) E) := (hT n M (Fin m) E hE Finset.univ).1
    have hsplit : ∀ v : ℂ, e.conjAlgEquiv ℂ (PiJ (m + 1) E v) =
        lift (PiJ m E v) * PiJ 1 (tE Finset.univ E) v := by
      intro v
      rw [lift_PiJ]
      unfold PiJ
      rw [List.ofFn_add, List.prod_append, map_mul, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
      simp only [Function.comp_def, map_add, AlgEquiv.commutes]
      congr 2
      · congr 1; funext i; congr 1; exact conj_eq e fun x => LinearMap.congr_fun (h3 i) x
      · congr 1; funext j; congr 1; exact conj_eq e fun x => LinearMap.congr_fun (h4 j) x
    have hq : e.conjAlgEquiv ℂ (qdet (tE (Finset.univ : Finset (Fin (m + 1))) E) u) =
        qdet (tE (Finset.univ : Finset (Fin 1)) (tE (Finset.univ : Finset (Fin m)) E)) u := by
      rw [← AlgEquiv.coe_toAlgHom, qdet_map]
      congr 1; funext a b
      exact conj_eq e fun x => LinearMap.congr_fun (h2 a b) x
    have hl : e.conjAlgEquiv ℂ (lift (qdet E u)) = lift (lift (qdet E u)) :=
      conj_eq e fun x => LinearMap.congr_fun (h5 _) x
    apply (e.conjAlgEquiv ℂ).injective
    rw [map_mul, map_mul, hsplit, hsplit, hq, hl, mul_assoc, one hT hJ hQ hC _ hG, ← mul_assoc, ← lift_mul, ih M E hE,
      lift_mul, mul_assoc]
end PositivityTheory.Rg.Cz
