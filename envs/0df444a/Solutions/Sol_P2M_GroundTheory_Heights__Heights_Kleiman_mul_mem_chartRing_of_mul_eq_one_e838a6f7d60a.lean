-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mul_mem_chartRing_of_mul_eq_one_e838a6f7d60a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:59:12.69969+00:00
-- url     : https://prove2.me/submissions/4dbc7e6b-c1c0-4cb6-8a5d-05f2b11076fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionSystems
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle

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
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {S : Type u} [CommRing S] {Ω : Type w} [Field Ω]
    [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω} {I : Chart x} {P M : Submodule (chartRing S x I) Ω}
    (hPM : P * M = 1) {q m : Ω} (hq : q ∈ P) (hm : m ∈ M) : q * m ∈ chartRing S x I := by
  have := Submodule.mul_mem_mul hq hm
  rw [hPM, Submodule.mem_one] at this
  obtain ⟨c, hc⟩ := this
  rw [← hc]; exact c.2
end GroundTheory.Heights₂.Heights.Kleiman
