-- Prove2me | solution 1 for UpperTheory.Reformulated.B.CasimirCommutation.casComm_casK_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:07:41.064703+00:00
-- url     : https://prove2.me/submissions/322eaeba-c61c-40d6-a572-e6d0d403145e

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CasimirCommutation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.CasimirCommutation
theorem _root_.solution :
    ∀ {A : Type} [inst : Ring A] {n : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → A),
      Formalism.REAL.GlRel E → ∀ (c d : Fin n), ε c = ε d → Formalism.REAL.CasK ε E * E c d = E c d * Formalism.REAL.CasK ε E := by
  intro A _ n ε E h c d hcd
  have key : ∀ a b, E a b * E b a * E c d - E c d * (E a b * E b a) =
      E a b * (if a = c then E b d else 0) - E a b * (if d = b then E c a else 0)
        + (if b = c then E a d else 0) * E b a - (if d = a then E c b else 0) * E b a := by
    intro a b
    have h1 := h b a c d
    have h2 := h a b c d
    have : E a b * (if a = c then E b d else 0) - E a b * (if d = b then E c a else 0)
        + (if b = c then E a d else 0) * E b a - (if d = a then E c b else 0) * E b a
        = E a b * ((if a = c then E b d else 0) - (if d = b then E c a else 0))
          + ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * E b a := by
      noncomm_ring
    rw [this, ← h1, ← h2]
    noncomm_ring
  have S1 : ∑ a, ∑ b, (if ε a = ε b then E a b * (if a = c then E b d else 0) else 0)
      = ∑ b, if ε c = ε b then E c b * E b d else 0 := by
    rw [Finset.sum_eq_single c (fun a _ ha => by simp [ha]) (by simp)]
    simp
  have S4 : ∑ a, ∑ b, (if ε a = ε b then (if d = a then E c b else 0) * E b a else 0)
      = ∑ b, if ε d = ε b then E c b * E b d else 0 := by
    rw [Finset.sum_eq_single d (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
    simp
  have S2 : ∑ a, ∑ b, (if ε a = ε b then E a b * (if d = b then E c a else 0) else 0)
      = ∑ a, if ε a = ε d then E a d * E c a else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single d (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  have S3 : ∑ a, ∑ b, (if ε a = ε b then (if b = c then E a d else 0) * E b a else 0)
      = ∑ a, if ε a = ε c then E a d * E c a else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have e : Formalism.REAL.CasK ε E * E c d - E c d * Formalism.REAL.CasK ε E =
      ∑ a, ∑ b, (if ε a = ε b then E a b * E b a * E c d - E c d * (E a b * E b a) else 0) := by
    simp only [Formalism.REAL.CasK, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  have e2 : ∑ a, ∑ b, (if ε a = ε b then E a b * E b a * E c d - E c d * (E a b * E b a) else 0)
      = ∑ a, ∑ b, (if ε a = ε b then E a b * (if a = c then E b d else 0) else 0)
        - ∑ a, ∑ b, (if ε a = ε b then E a b * (if d = b then E c a else 0) else 0)
        + ∑ a, ∑ b, (if ε a = ε b then (if b = c then E a d else 0) * E b a else 0)
        - ∑ a, ∑ b, (if ε a = ε b then (if d = a then E c b else 0) * E b a else 0) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [key]
    split_ifs <;> simp
  rw [← sub_eq_zero, e, e2, S1, S2, S3, S4, hcd]
  abel
end UpperTheory.Reformulated.B.CasimirCommutation
