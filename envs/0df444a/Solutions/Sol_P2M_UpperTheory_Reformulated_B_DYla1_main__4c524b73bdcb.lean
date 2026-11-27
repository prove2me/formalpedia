-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_DYla1_main__4c524b73bdcb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:17:39.227555+00:00
-- url     : https://prove2.me/submissions/84e94aef-023e-450d-8c65-6d1e4bf83d9e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisFurther

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.DYla1.main
theorem _root_.solution.{u_3, u_4, u_5} :
    ∀ {o : Type u_3} {ι : Type u_4} {S : Type u_5} [Fintype ι] [inst : CommRing o] [inst_1 : CommRing S]
      [inst_2 : Algebra o S] {f : MvPolynomial ι o} {d : ℕ},
      f.IsHomogeneous d →
        ∀ (c : S) (v : ι → S),
          (MvPolynomial.aeval fun (i : ι) ↦ c * v i : MvPolynomial ι o → S) f =
            c ^ d * (MvPolynomial.aeval v : MvPolynomial ι o → S) f := by
  intro o ι S _ _ _ _ f d hf c v
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
    MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have h := hf (MvPolynomial.mem_support_iff.mp hm)
    have h' : m.degree = d := by
      rw [Finsupp.degree_eq_weight_one]
      exact h
    rw [← h', Finsupp.degree_eq_sum]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring
end UpperTheory.Reformulated.B.DYla1.main
