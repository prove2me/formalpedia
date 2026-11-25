-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qf29.der_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:30:47.382346+00:00
-- url     : https://prove2.me/submissions/bb025dd6-31d3-4631-8a21-8ff4be6cfea8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DerAeval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qf29
theorem _root_.solution :
    ∀ {F : Type} [inst : Field F] {δ : F → F},
      Formalism.L2.Pj.GenericSectionMinimum.IsDer δ →
        ∀ {E : Type} [inst_1 : CommRing E] [inst_2 : Algebra E F],
          (∀ (e : E), δ ((Algebra.algebraMap E F : E → F) e) = (0 : F)) →
            ∀ {σ : Type} [inst_3 : Fintype σ] [DecidableEq σ] (t : σ → F) (P : MvPolynomial σ E),
              δ ((MvPolynomial.aeval t : MvPolynomial σ E → F) P) =
                ∑ i : σ,
                  (MvPolynomial.aeval t : MvPolynomial σ E → F)
                      ((MvPolynomial.pderiv i : MvPolynomial σ E → MvPolynomial σ E) P) *
                    δ (t i) := by
  intro F _ δ hδ E _ _ hE σ _ _ t P
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C, MvPolynomial.pderiv_C, map_zero, zero_mul,
      Finset.sum_const_zero]
    exact hE a
  | add p q hp hq =>
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    rw [hδ.add, hp, hq]
  | mul_X p n hp =>
    have h : ∀ i : σ,
        MvPolynomial.aeval t (MvPolynomial.pderiv i (p * MvPolynomial.X n)) * δ (t i) =
          (if i = n then MvPolynomial.aeval t p * δ (t i) else 0) +
            t n * (MvPolynomial.aeval t (MvPolynomial.pderiv i p) * δ (t i)) := by
      intro i
      rw [MvPolynomial.pderiv_mul]
      by_cases hi : i = n
      · subst hi
        rw [MvPolynomial.pderiv_X_self, if_pos rfl]
        simp only [map_add, map_mul, MvPolynomial.aeval_X, mul_one]
        ring
      · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hi), if_neg hi]
        simp only [map_mul, MvPolynomial.aeval_X, mul_zero, add_zero]
        ring
    rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, ← Finset.mul_sum, ← hp,
      Finset.sum_ite_eq' Finset.univ n, if_pos (Finset.mem_univ n), map_mul,
      MvPolynomial.aeval_X, hδ.mul]
end UpperTheory.Reformulated.B.Qf29
