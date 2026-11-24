-- Prove2me | solution 1 for P2M_Formalism_L2_Pj_CurveCount_eval__mul_homog_942dcdf5c407
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:14.335011+00:00
-- url     : https://prove2.me/submissions/c572d9f2-c057-4cea-a261-327c469a6530

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CurveCountA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.CurveCount
open MvPolynomial
namespace Formalism.L2.Pj.CurveCount
theorem _root_.solution {R S σ : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (c : S) (g : σ → S)
    {P : MvPolynomial σ R} {k : ℕ} (hP : P.IsHomogeneous k) :
    P.eval₂ f (fun i => c * g i) = c ^ k * P.eval₂ f g := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = k := by
    have h := hP (MvPolynomial.mem_support_iff.1 hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring
end Formalism.L2.Pj.CurveCount
