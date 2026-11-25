-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.IdCellInSW.alg_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:54:14.851222+00:00
-- url     : https://prove2.me/submissions/661d8884-5258-4708-ae49-2064abc4a0e7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdentityCellTrace_ExistsSmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdentityCellTrace_AlgIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.IdCellInSW
variable {E : Type} [Field E] [StarRing E] {r : ℕ}
namespace PI.UnitaryGroupMassFormula.IdCellInSW
theorem _root_.solution (α α' β β' : Fin r → E) (G s : Fin r → Fin r → E)
    (hs : ∀ a b, G a b + s a b + star (s b a) = 0) :
    (∑ a, α' a * star (β a)) + (∑ a, star (α a) * β' a) +
      (∑ a, ∑ b, star (α a) * (α' b * G a b)) +
      (∑ a, (-β' a + ∑ b, s a b * α' b) * star (α a)) +
      (∑ a, star (-β a + ∑ b, s a b * α b) * α' a) = 0 := by
  have key : ∀ a b, star (α a) * (α' b * G a b) + s a b * α' b * star (α a) +
      star (s b a) * star (α a) * α' b = 0 := by
    intro a b
    have := hs a b
    linear_combination (star (α a) * α' b) * this
  have h1 : (∑ a, (-β' a + ∑ b, s a b * α' b) * star (α a)) =
      -(∑ a, star (α a) * β' a) + ∑ a, ∑ b, s a b * α' b * star (α a) := by
    simp only [add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_mul]
    congr 1
    exact congrArg Neg.neg (Finset.sum_congr rfl fun a _ => mul_comm _ _)
  have h2 : (∑ a, star (-β a + ∑ b, s a b * α b) * α' a) =
      -(∑ a, α' a * star (β a)) + ∑ a, ∑ b, star (s b a) * star (α a) * α' b := by
    simp only [star_add, star_neg, star_sum, star_mul', add_mul, neg_mul, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, Finset.sum_mul]
    congr 1
    · exact congrArg Neg.neg (Finset.sum_congr rfl fun a _ => mul_comm _ _)
    · rw [Finset.sum_comm]
  rw [h1, h2]
  have h3 : (∑ a, ∑ b, star (α a) * (α' b * G a b)) + (∑ a, ∑ b, s a b * α' b * star (α a)) +
      (∑ a, ∑ b, star (s b a) * star (α a) * α' b) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun b _ => key a b
  linear_combination h3
end PI.UnitaryGroupMassFormula.IdCellInSW
