-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_mem_tgr_0b163f9c37ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:01.954114+00:00
-- url     : https://prove2.me/submissions/b597482a-501e-4a9a-bd1a-74ad2b891a29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_PsiOfIsHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_single_mem_tgr_1d4f2bbc1844
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_mem_tgr_ca561eb3db71

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
open MvPolynomial AddMonoidAlgebra
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.TwistFin
variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω)
variable (S : Type u) [CommRing S] [Algebra S Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman.TwistFin
theorem _root_.solution {p : Poly (Sy S r) N} {d : ℕ} (hp : p.IsHomogeneous d) :
    phi x η S p ∈ tgr (d : ℤ) := by
  classical
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have hdeg : ∑ i ∈ μ.support, μ i = d := by
    have := hp (mem_support_iff.mp hμ)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  rw [phi, coe_eval₂Hom, eval₂_monomial]
  have h1 := psi_mem_tgr η S (MvPolynomial.coeff μ p)
  have h2 : (∏ i ∈ μ.support, (single ((1 : ℤ), (0 : ℤ)) (x i) : LA Ω) ^ μ i) ∈
      tgr (∑ i ∈ μ.support, ((μ i : ℕ) : ℤ)) := by
    refine SetLike.prod_mem_graded _ _ _ fun i _ => ?_
    simpa using SetLike.pow_mem_graded (μ i) (single_mem_tgr 1 0 (x i))
  have h3 := SetLike.mul_mem_graded h1 h2
  rw [zero_add, ← Nat.cast_sum, hdeg] at h3
  exact h3
end GroundTheory.Heights₂.Heights.Kleiman.TwistFin
