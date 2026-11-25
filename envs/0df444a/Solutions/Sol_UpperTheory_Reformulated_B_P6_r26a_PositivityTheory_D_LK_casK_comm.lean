-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.r26a.PositivityTheory.D.LK.casK_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:21:22.332568+00:00
-- url     : https://prove2.me/submissions/b17c36e9-338e-41a8-93e1-ca0f744046db

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_DoubleSumReduceSecond
import Theorems.Thm_UpperTheory_Reformulated_B_P6_r26a_commutator_casimir_term
import Theorems.Thm_UpperTheory_Reformulated_B_P6_r26a_double_sum_reduce_first
import Theorems.Thm_UpperTheory_Reformulated_B_P6_r26a_double_sum_reduce_fourth
import Theorems.Thm_UpperTheory_Reformulated_B_P6_r26a_double_sum_reduce_third
import Theorems.Thm_UpperTheory_Reformulated_B_P6_r26a_double_sum_reduce_second

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r26a
open scoped HSub SubNegMonoid AddGroup AddGroupWithOne Ring HMul Distrib OfNat Zero MulZeroClass Finset Semiring Fin Complex AddCommGroup Module Module.End
namespace UpperTheory.Reformulated.B.P6.r26a
namespace PositivityTheory.D.LK
theorem _root_.solution :
    ∀ {n : ℕ} {ε_h0 : Fin n → Bool} {V : Type} [inst_h2 : AddCommGroup V] [inst_h3 : _root_.Module ℂ V] {E : Fin n → Fin n → Module.End ℂ V}, PositivityTheory.D.DSIC.KRel ε_h0 E → ∀ {c d : Fin n}, ε_h0 c = ε_h0 d → Commute (E c d) (Formalism.REAL.CasK ε_h0 E) := by
  intro n ε V _ _ E hK c d hcd
  show E c d * Formalism.REAL.CasK ε E = Formalism.REAL.CasK ε E * E c d
  rw [← sub_eq_zero]
  have hsum : E c d * Formalism.REAL.CasK ε E - Formalism.REAL.CasK ε E * E c d
      = ∑ a : Fin n, ∑ b : Fin n, (E c d * (if ε a = ε b then E a b * E b a else 0)
          - (if ε a = ε b then E a b * E b a else 0) * E c d) := by
    unfold Formalism.REAL.CasK
    simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
  rw [hsum]
  simp only [commutator_casimir_term ε E hK hcd, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [double_sum_reduce_first, double_sum_reduce_fourth, double_sum_reduce_third, double_sum_reduce_second, hcd]
  simp
end PositivityTheory.D.LK
end UpperTheory.Reformulated.B.P6.r26a
