-- Prove2me | solution 1 for PI.WGL.LTA.rowDiv_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:20:35.166059+00:00
-- url     : https://prove2.me/submissions/c8838073-ab9a-4ab8-b88e-425ebf2194be

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleA
import Theorems.Thm_PI_WGL_LTA_rowDiv_prod
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
open PI PI.WGL PI.WGL.LTA
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL.LTA
theorem _root_.solution {r c n K : ℕ} (e : Fin n → Fin r) (sz : Fin K → ℕ)
    (G : ∀ k, (Fin (sz k) → Fin n) → MvPolynomial (Fin r × Fin c) ℤ) (hG : ∀ k, Exp e (G k))
    (C0 : MvPolynomial (Fin r × Fin c) ℤ) (a b : Fin n) (hC : rowGen ℤ (e a) (e b) C0 = Polynomial.C C0)
    (t : ℕ) (d : (∀ k, Fin (sz k) → Fin n) →₀ ℤ) :
    rowDiv ℤ (e a) (e b) t (Finsupp.linearCombination ℤ (fun J => C0 * ∏ k, G k (J k)) d) =
      Finsupp.linearCombination ℤ (fun J => C0 * ∏ k, G k (J k)) (tlin sz a b t d) := by
  classical
  have hsm : ∀ (z : ℤ) (x : MvPolynomial (Fin r × Fin c) ℤ),
      rowDiv ℤ (e a) (e b) t (z • x) = z • rowDiv ℤ (e a) (e b) t x := by
    intro z x
    unfold rowDiv
    rw [map_smul, Polynomial.coeff_smul]
  refine Finsupp.induction_linear d ?_ ?_ ?_
  · unfold rowDiv
    simp
  · intro f g hf hg
    rw [map_add, map_add, map_add]
    unfold rowDiv at hf hg ⊢
    rw [map_add, Polynomial.coeff_add, hf, hg]
  · intro J c
    unfold tlin
    rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul, hsm,
      rowDiv_prod e sz G hG C0 a b hC t J]
    congr 1
    unfold tmat
    rw [map_sum]
    refine Finset.sum_congr rfl fun F _ => ?_
    split_ifs
    · rw [Finsupp.linearCombination_single, one_smul]
    · rw [map_zero]
end PI.WGL.LTA
