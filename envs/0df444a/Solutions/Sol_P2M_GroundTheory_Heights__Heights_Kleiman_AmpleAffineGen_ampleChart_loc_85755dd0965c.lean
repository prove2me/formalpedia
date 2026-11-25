-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_ampleChart_loc_85755dd0965c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:52:23.2003+00:00
-- url     : https://prove2.me/submissions/3a7bf1fc-9cd2-43e4-b99f-2451f896fde4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_of_eq_45744a7bcb93
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_powBundle_toSubSystem_418f6a814041


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
theorem _root_.solution (H : LineBundle S x) {m : ℕ} {h : Ω} (I J : Chart x) {a : Ω}
    (ha : a ∈ ampleChart H.toSubSystem m h (unionChart I J)) :
    ∃ D : ℕ, chartRatio I J ^ D * a ∈ ampleChart H.toSubSystem m h I := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨D, hD⟩ := exists_pow_mul_mem_of_eq (H.powBundle (m * n))
    (LineBundle.powBundle_toSubSystem H _) I J hn
  exact ⟨D, n, by rw [mul_assoc]; exact hD⟩
end GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
