-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_pow_eq_map_expand_ad624b380e19
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:45.511612+00:00
-- url     : https://prove2.me/submissions/31979faf-8ebc-418d-876b-bfb7baad0f5e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_NoetherCharPLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open Polynomial
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {σ k k' : Type*} [Field k] [Field k'] [Algebra k k'] (p : ℕ)
    [Fact p.Prime] [CharP k' p] (e : ℕ) (N : MvPolynomial σ k)
    (hN : ∀ m, ∃ z : k', z ^ p ^ e = algebraMap k k' (N.coeff m)) :
    ∃ N' : MvPolynomial σ k',
      N' ^ p ^ e = MvPolynomial.map (algebraMap k k') (MvPolynomial.expand (p ^ e) N) := by
  choose r hr using hN
  refine ⟨∑ m ∈ N.support, MvPolynomial.monomial m (r m), ?_⟩
  rw [← MvPolynomial.map_iterateFrobenius_expand p, map_sum, map_sum]
  conv_rhs => rw [N.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [MvPolynomial.expand_monomial, iterateFrobenius_def, hr]
end GroundTheory.Heights₂.Heights.FieldNumbers
