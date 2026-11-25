-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.PStepFormula.one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:57:20.334593+00:00
-- url     : https://prove2.me/submissions/245edd52-7d15-4935-8ff1-ecfed290481e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepFormulaA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepFormula
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_PiJ_one
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_alt_swap
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_app_swap
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_conj_eq
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_conj_xJ
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_curF_Om_l
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_curF_Om_r
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_ext_of_alt
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_glRel_map
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_liftA_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_lift_PiJ
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_qdet_map
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_rot_last
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_rot_nat
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_sum_lt_cast
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_sum_swap
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_comm_pm
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_mul
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_mul
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
open PositivityTheory.Rg.Cz.PStepFormula
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.PStepFormula
theorem _root_.solution (hT : TensorGl) (hJ : JMComm) (hQ : PiQdet) (hC : Curry) (E : Fin n → Fin n → Module.End ℂ M)
    (hE : GlRel E) (u : ℂ) :
    (PiJ 1 E u * qdet (tE (Finset.univ : Finset (Fin 1)) E) u : Module.End ℂ (TV n M (Fin 1))) =
      lift (qdet E u) * PiJ 1 E (u + 1) := by
  obtain ⟨hbij, -, h3, h4, -, -, h7⟩ := hC n M E 1 n
  set e := LinearEquiv.ofBijective (curF n M 1 n) hbij
  have hG : GlRel (tE (Finset.univ : Finset (Fin 1)) E) := (hT n M (Fin 1) E hE Finset.univ).1
  have hE' : GlRel (fun a b => (lift (E a b) : Module.End ℂ (TV n M (Fin 1)))) :=
    glRel_map (liftA n M (Fin 1)) hE
  have hsw : ∀ a b : Fin n, e.conjAlgEquiv ℂ (pm (Equiv.swap (Fin.natAdd 1 a) (Fin.natAdd 1 b))) =
      pm (Equiv.swap a b) := fun a b => conj_eq e fun x => LinearMap.congr_fun (h7 a b) x
  have hOr : ∀ j : Fin n, e.conjAlgEquiv ℂ (Om E (Fin.natAdd 1 j)) = Om (fun a b => lift (E a b)) j :=
    fun j => conj_eq e fun x => curF_Om_r E j x
  have hOl : e.conjAlgEquiv ℂ (Om E (Fin.castAdd n (0 : Fin 1))) = lift (Om E 0) :=
    conj_eq e fun x => curF_Om_l E 0 x
  have s1 : e.conjAlgEquiv ℂ (PiJ (1 + n) E u) = lift (PiJ 1 E u) * PiJ n (tE Finset.univ E) u := by
    rw [lift_PiJ]
    unfold PiJ
    rw [List.ofFn_add, List.prod_append, map_mul, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    simp only [Function.comp_def, map_add, AlgEquiv.commutes]
    congr 2
    · congr 1; funext i; congr 1; exact conj_eq e fun x => LinearMap.congr_fun (h3 i) x
    · congr 1; funext j; congr 1; exact conj_eq e fun x => LinearMap.congr_fun (h4 j) x
  set Q : Module.End ℂ (TV n M (Fin (1 + n))) :=
    ∑ j : Fin n, pm (Equiv.swap (Fin.natAdd 1 j) (Fin.castAdd n 0)) with hQdef
  have s2 : e.conjAlgEquiv ℂ (PiJ (1 + n) E u) =
      PiJ n (fun a b => lift (E a b)) u * (algebraMap ℂ _ u + lift (Om E 0) + e.conjAlgEquiv ℂ Q) := by
    have hR : pm (rot n) * PiJ (1 + n) E u * pm (rot n)⁻¹ = PiJ (1 + n) E u := by
      rw [← ((hJ n M E hE (1 + n)).2.2 u (rot n)).eq, mul_assoc, ← pm_mul, mul_inv_cancel, pm_one, mul_one]
    let eρ : TV n M (Fin (1 + n)) ≃ₗ[ℂ] TV n M (Fin (1 + n)) :=
      LinearEquiv.ofLinear (pm (rot n)) (pm (rot n)⁻¹)
        (by rw [← Module.End.mul_eq_comp, ← pm_mul, mul_inv_cancel, pm_one]; rfl)
        (by rw [← Module.End.mul_eq_comp, ← pm_mul, inv_mul_cancel, pm_one]; rfl)
    have hΨ : ∀ T, eρ.conjAlgEquiv ℂ T = pm (rot n) * T * pm (rot n)⁻¹ := fun T => rfl
    rw [← hR, ← hΨ]
    unfold PiJ
    rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn, List.ofFn_congr (Nat.add_comm 1 n),
      List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
    simp only [Function.comp_apply, map_add, AlgEquiv.commutes]
    congr 1
    · congr 1; congr 1; funext j; congr 1
      have hk : (Fin.cast (Nat.add_comm 1 n).symm j.castSucc : Fin (1 + n)) = ⟨j, by omega⟩ := Fin.ext (by simp)
      rw [hΨ, conj_xJ hT E hE, hk, rot_nat, map_add, hOr, xJ, sum_lt_cast _ (by simp), map_sum]
      congr 1
      refine Finset.sum_congr (Finset.filter_congr fun i _ => Iff.rfl) fun i _ => ?_
      rw [rot_nat, hsw]
    · rw [hΨ, conj_xJ hT E hE, rot_last _ (by simp), map_add, hOl, sum_lt_cast _ (by simp), hQdef, map_sum, map_sum,
        add_assoc]
      congr 2
      refine Finset.sum_congr (Finset.filter_true_of_mem fun i _ => by simp) fun i _ => ?_
      rw [rot_nat]
  have hQalt : e.conjAlgEquiv ℂ Q * alt Finset.univ = alt Finset.univ := by
    apply LinearMap.ext; intro g
    rw [Module.End.mul_apply]
    funext J I
    have hsymm : ∀ (y : TV n (TV n M (Fin 1)) (Fin n)) (I' : Fin 1 → Fin n) (J' : Fin n → Fin n),
        e.symm y (Fin.append I' J') = y J' I' := fun y I' J' =>
      congrFun (congrFun (e.apply_symm_apply y) J') I'
    show (Q (e.symm (alt Finset.univ g))) (Fin.append I J) = _
    rw [hQdef, LinearMap.sum_apply, Finset.sum_apply]
    simp only [pm_apply, app_swap, hsymm]
    exact sum_swap (fun J I => alt Finset.univ g J I) (fun J a b hab => alt_swap g J a b hab) J I
  have hq1 := hQ n _ _ hG u
  have hq2 := hQ n _ _ hE' u
  have hqE : qdet (fun a b => (lift (E a b) : Module.End ℂ (TV n M (Fin 1)))) u = lift (qdet E u) :=
    (qdet_map (liftA n M (Fin 1)) E u).symm
  have hcomm : ∀ B : Module.End ℂ (TV n M (Fin 1)),
      (alt Finset.univ : Module.End ℂ (TV n (TV n M (Fin 1)) (Fin n))) * lift B = lift B * alt Finset.univ := by
    intro B
    simp only [alt, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, (lift_comm_pm B _).eq]
  have hl : (lift (algebraMap ℂ _ (u + 1) + Om E 0) : Module.End ℂ (TV n (TV n M (Fin 1)) (Fin n))) =
      algebraMap ℂ _ u + lift (Om E 0) + 1 := by
    rw [← liftA_apply, map_add, AlgHom.commutes, liftA_apply, map_add, map_one]; abel
  rw [PiJ_one E (u + 1)]
  apply ext_of_alt (n := n)
  calc lift (PiJ 1 E u * qdet (tE Finset.univ E) u) * alt Finset.univ
      = lift (PiJ 1 E u) * (PiJ n (tE Finset.univ E) u * alt Finset.univ) := by rw [hq1, lift_mul, mul_assoc]
    _ = e.conjAlgEquiv ℂ (PiJ (1 + n) E u) * alt Finset.univ := by rw [s1, mul_assoc]
    _ = PiJ n (fun a b => lift (E a b)) u * (lift (algebraMap ℂ _ (u + 1) + Om E 0) * alt Finset.univ) := by
        rw [s2, mul_assoc, hl, add_mul, hQalt, add_mul _ 1, one_mul]
    _ = PiJ n (fun a b => lift (E a b)) u * alt Finset.univ * lift (algebraMap ℂ _ (u + 1) + Om E 0) := by
        rw [← hcomm, mul_assoc]
    _ = lift (lift (qdet E u) * (algebraMap ℂ _ (u + 1) + Om E 0)) * alt Finset.univ := by
        rw [hq2, hqE, mul_assoc, hcomm, ← mul_assoc, ← lift_mul]
end PositivityTheory.Rg.Cz.PStepFormula
