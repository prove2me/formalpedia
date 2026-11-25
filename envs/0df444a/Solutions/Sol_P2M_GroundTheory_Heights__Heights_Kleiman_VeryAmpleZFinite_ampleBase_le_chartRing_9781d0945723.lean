-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFinite_ampleBase_le_chartRing_9781d0945723
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:17:47.139949+00:00
-- url     : https://prove2.me/submissions/098bd91a-6390-471f-8b42-79ad282e51a5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZFinite

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
open Filter
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFinite
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {r : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFinite
theorem _root_.solution {h : Fin (r + 1) → Ω} (J : Chart h) {j : Fin (r + 1)} (hj : j ∈ J.1) :
    ampleBase (S := S) h j ≤ chartRing S h J := by
  rw [ampleBase, Algebra.adjoin_le_iff]
  rintro _ ⟨l, rfl⟩
  exact ⟨MvPolynomial.X l, MvPolynomial.X j, 1, X_mem_monos hj, MvPolynomial.isHomogeneous_X S l,
    MvPolynomial.isHomogeneous_X S j, by simp⟩
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFinite
