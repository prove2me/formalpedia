-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_sub_ne_bot_cb59329d6f45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:18:30.025273+00:00
-- url     : https://prove2.me/submissions/7b5102cd-d096-4a88-8ae6-5e16d6d4c88e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrictGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictGenerated

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
open GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}
  {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated
theorem _root_.solution (Q' : LineBundle S y) (J : Chart y) : Q'.toSubSystem.sub J ≠ ⊥ := by
  intro h0
  obtain ⟨Q'', hQ''⟩ := Q'.invertible J
  have h1 : (1 : K') ∈ (1 : Submodule (chartRing S y J) K') := Submodule.mem_one.mpr ⟨1, map_one _⟩
  rw [← hQ''] at h1
  change (1 : K') ∈ Q'.toSubSystem.sub J * Q'' at h1
  rw [h0, Submodule.bot_mul] at h1
  exact one_ne_zero ((Submodule.mem_bot _).mp h1)
end GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated
