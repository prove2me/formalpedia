-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_loc_90c900bcc943
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:55:21.197882+00:00
-- url     : https://prove2.me/submissions/7fc0519b-71d9-4740-96f2-9592d1574928

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_of_eq_45744a7bcb93
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_tensorProd_powBundle_7fe273c34225

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
theorem _root_.solution (Q H : LineBundle S x) {m b : ℕ} {h : Ω} (I J : Chart x) {z : Ω}
    (hz : z ∈ secChart Q.toSubSystem H.toSubSystem m b h (unionChart I J)) :
    ∃ D : ℕ, chartRatio I J ^ D * z ∈ secChart Q.toSubSystem H.toSubSystem m b h I := by
  obtain ⟨k, hk⟩ := hz
  obtain ⟨D, hD⟩ := exists_pow_mul_mem_of_eq (Q.tensorProd (H.powBundle (b + m * k)))
    (tensorProd_powBundle Q H _) I J hk
  exact ⟨D, k, by rw [mul_assoc]; exact hD⟩
end GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
