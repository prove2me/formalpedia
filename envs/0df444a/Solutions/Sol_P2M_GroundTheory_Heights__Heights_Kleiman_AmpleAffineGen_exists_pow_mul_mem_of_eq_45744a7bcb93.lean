-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_of_eq_45744a7bcb93
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:34:32.77167+00:00
-- url     : https://prove2.me/submissions/194270e0-6297-4580-89e2-4ee0f64166e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_sub_613bf1440878

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
open GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
theorem _root_.solution (L : LineBundle S x) {F : SubSystem S x Ω}
    (hL : L.toSubSystem = F) (I J : Chart x) {y : Ω} (hy : y ∈ F.sub (unionChart I J)) :
    ∃ D : ℕ, chartRatio I J ^ D * y ∈ F.sub I := by
  subst hL
  exact exists_pow_mul_mem_sub L.toSubFamily I J hy
end GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
