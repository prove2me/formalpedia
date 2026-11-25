-- Prove2me | solution 1 for PI.WGL.LTA.applyWord_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:17.437986+00:00
-- url     : https://prove2.me/submissions/83a79ad8-4c87-4e14-a09c-1d8737fb7f82

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleA
import Theorems.Thm_PI_WGL_LTA_rowDiv_comb

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
    (C0 : MvPolynomial (Fin r × Fin c) ℤ)
    (hC : ∀ a b : Fin n, a ≠ b → rowGen ℤ (e a) (e b) C0 = Polynomial.C C0) :
    ∀ (w : List (Fin n × Fin n × ℕ)), OffDiag w → ∀ d,
      applyWord ℤ (w.map fun x => (e x.1, e x.2.1, x.2.2))
        (Finsupp.linearCombination ℤ (fun J => C0 * ∏ k, G k (J k)) d) =
      Finsupp.linearCombination ℤ (fun J => C0 * ∏ k, G k (J k)) (twd sz w d)
  | [], _, _ => rfl
  | x :: w, hw, d => by
    have hx : x.1 ≠ x.2.1 := hw x List.mem_cons_self
    have hw' : OffDiag w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    show rowDiv ℤ (e x.1) (e x.2.1) x.2.2 (applyWord ℤ (w.map fun x => (e x.1, e x.2.1, x.2.2))
        (Finsupp.linearCombination ℤ (fun J => C0 * ∏ k, G k (J k)) d)) = _
    rw [solution e sz G hG C0 hC w hw' d, rowDiv_comb e sz G hG C0 x.1 x.2.1 (hC _ _ hx)]
    rfl
end PI.WGL.LTA
