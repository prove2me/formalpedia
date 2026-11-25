-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_aeval_div_pow_3ee1d0390a06
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:10:01.819166+00:00
-- url     : https://prove2.me/submissions/eccf03c9-eade-4092-bc26-90b199adfc3e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AmpleRingFiniteTypeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleRingFiniteType

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.AmpleRingFiniteType
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.AmpleRingFiniteType
theorem _root_.solution {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) (c : Ω) :
    aeval (fun i => x i / c) f = aeval x f / c ^ e := by
  conv_lhs => rw [← f.support_sum_monomial_coeff]
  conv_rhs => rw [← f.support_sum_monomial_coeff]
  simp only [map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hdeg := hf (mem_support_iff.mp hμ)
  simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum] at hdeg
  simp only [aeval_monomial, Finsupp.prod, div_pow, Finset.prod_div_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg, mul_div_assoc]
end GroundTheory.Heights₂.Heights.Kleiman.AmpleRingFiniteType
