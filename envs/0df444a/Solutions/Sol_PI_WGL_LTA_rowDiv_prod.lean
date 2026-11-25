-- Prove2me | solution 1 for PI.WGL.LTA.rowDiv_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:08:55.280822+00:00
-- url     : https://prove2.me/submissions/d33c127e-75ce-4641-ae85-a2ae3e173769

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTA
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL.LTA
theorem _root_.solution {r c n K : ℕ} (e : Fin n → Fin r) (sz : Fin K → ℕ)
    (G : ∀ k, (Fin (sz k) → Fin n) → MvPolynomial (Fin r × Fin c) ℤ) (hG : ∀ k, Exp e (G k))
    (C0 : MvPolynomial (Fin r × Fin c) ℤ) (a b : Fin n) (hC : rowGen ℤ (e a) (e b) C0 = Polynomial.C C0)
    (t : ℕ) (I : ∀ k, Fin (sz k) → Fin n) :
    rowDiv ℤ (e a) (e b) t (C0 * ∏ k, G k (I k)) =
      ∑ F : (∀ k, Finset (Fin (sz k))), if (∀ k, ∀ p ∈ F k, I k p = b) ∧ ∑ k, (F k).card = t then
        C0 * ∏ k, G k (upd (I k) (F k) a) else 0 := by
  classical
  unfold rowDiv
  rw [map_mul, hC, map_prod, Finset.prod_congr rfl (fun k _ => hG k a b (I k)), Fintype.prod_sum,
    Finset.mul_sum, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [Finset.prod_ite_zero]
  by_cases hA : ∀ k ∈ (Finset.univ : Finset (Fin K)), ∀ p ∈ F k, I k p = b
  · rw [if_pos hA, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← map_prod Polynomial.C]
    rw [show Polynomial.C C0 * (Polynomial.X ^ (∑ k, (F k).card) *
          Polynomial.C (∏ k, G k (upd (I k) (F k) a))) =
        Polynomial.monomial (∑ k, (F k).card) (C0 * ∏ k, G k (upd (I k) (F k) a)) by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul]
      ring]
    rw [Polynomial.coeff_monomial]
    have hA' : ∀ k, ∀ p ∈ F k, I k p = b := fun k => hA k (Finset.mem_univ k)
    by_cases hs : ∑ k, (F k).card = t
    · rw [if_pos hs, if_pos ⟨hA', hs⟩]
    · rw [if_neg hs, if_neg (fun h => hs h.2)]
  · rw [if_neg hA, mul_zero, Polynomial.coeff_zero, if_neg]
    intro h
    exact hA (fun k _ => h.1 k)
end PI.WGL.LTA
