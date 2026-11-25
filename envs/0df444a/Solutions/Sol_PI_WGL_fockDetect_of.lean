-- Prove2me | solution 1 for PI.WGL.fockDetect_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:50:23.679275+00:00
-- url     : https://prove2.me/submissions/9833aece-5c19-4d4d-9ec9-af0f72e567ea

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftFock
import Theorems.Thm_PI_WGL_Fock6_weight_indicator_eq_degree
import Theorems.Thm_PI_WGL_Fock6_word_reduce
import Theorems.Thm_PI_WGL_Fock6_word_adj
import Theorems.Thm_PI_WGL_Fock6_transposeWord_transposeWord
import Theorems.Thm_PI_WGL_Fock6_transposeWord_liftWord
import Theorems.Thm_PI_WGL_Fock6_offDiag_transpose
import Theorems.Thm_PI_WGL_Fock6_natW_anti
import Theorems.Thm_PI_WGL_Fock6_eqv_word
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockPos
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwRowWeight
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.REAL MvPolynomial
open Fock6
namespace PI.WGL
theorem _root_.solution (h3 : PI.HwIrred) (hD : EqvDiv) : FockDetect := by
  intro n N h lam sg _ io0 hEqv hext u hu hort
  set E : MvPolynomial (Fin n × Fin n) ℂ := extremal ℂ n sg with hE
  have hEmem : E ∈ nablaSq ℂ n sg := hwMem ℂ n n le_rfl sg.natW (natW_anti sg)
  have hErow : ∀ c : Fin n, ∃ H : ℤ, IsWeightedHomogeneous (rw1 c) E H := by
    intro c
    refine ⟨((rowNu (r := n) sg.natW c : ℕ) : ℤ), fun m hm => ?_⟩
    have := hwRowWeight ℂ n n le_rfl sg.natW (natW_anti sg) hm
    rw [weight_indicator_eq_degree]
    exact congrArg (fun v : Fin n → ℕ => ((v c : ℕ) : ℤ)) this

  have key : ∀ w, OffDiag w → fockF (io0 u) (io0 (applyWord ℂ w E)) = 0 := by
    intro w hw
    rw [(eqv_word hD h sg lam io0 hEqv w hw E hEmem).2, hext]
    have e := word_adj (transposeWord (liftWord h w)) (io0 u) (xi ℂ h lam sg)
    rw [transposeWord_transposeWord, transposeWord_liftWord] at e
    rw [← e]
    exact hort _ (offDiag_transpose hw)

  let S : Set (MvPolynomial (Fin n × Fin n) ℂ) := {f | ∃ w, OffDiag w ∧ f = applyWord ℂ w E}
  have hspan : u ∈ Submodule.span ℂ S := by
    have hu' : u ∈ delSq ℂ n sg := (h3 n sg).1 ▸ hu
    refine (Submodule.span_le.mpr ?_) hu'
    rintro _ ⟨w, rfl⟩
    obtain ⟨w', hw', z, hz⟩ := word_reduce E hErow w
    show applyWord ℂ w E ∈ Submodule.span ℂ S
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w', hw', rfl⟩)

  let P : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) :=
    { carrier := {y | fockF (io0 u) (io0 y) = 0}
      zero_mem' := by simp [fockF]
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq, map_add] at *
        unfold fockF at *
        rw [← zero_add (0 : ℂ)]
        nth_rewrite 1 [← ha]
        rw [← hb, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [coeff_add, star_add]
        ring
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq, map_smul] at *
        unfold fockF at *
        have : ∑ m ∈ (io0 u).support, (io0 u).coeff m * star ((c • io0 a).coeff m) *
            ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) =
            star c * ∑ m ∈ (io0 u).support, (io0 u).coeff m * star ((io0 a).coeff m) *
              ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          simp only [coeff_smul, smul_eq_mul, star_mul']
          ring
        rw [this, ha, mul_zero] }
  have hSP : Submodule.span ℂ S ≤ P := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    exact key w hw
  have h0 : fockF (io0 u) (io0 u) = 0 := hSP hspan
  by_contra hne
  have := (fockPos _ (io0 u) hne).1
  rw [h0] at this
  simp at this
end PI.WGL
