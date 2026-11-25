-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_mul_mem_chartRing_54282771e4c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:54:14.441865+00:00
-- url     : https://prove2.me/submissions/b2c18914-ea00-4f0d-8b81-9ce99b39dc30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulMemSecsTwistIdealSys
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_lift_frac_3934fd766e28

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial Kleiman
noncomputable section
variable {S : Type*} [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal] {O : Type*} [CommRing O] [Algebra S O]
  [IsLocalization.AtPrime O 𝔪] {Ω : Type*} [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω]
  {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
theorem _root_.solution {I : Chart x} {a : Ω} (ha : a ∈ chartRing O x I) :
    ∃ t : S, t ∉ 𝔪 ∧ algebraMap S Ω t * a ∈ chartRing S x I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  obtain ⟨t, ht, g, s₀, hg, hs₀, hs₀e, -, hval⟩ := exists_lift_frac 𝔪 hf hs hse
  exact ⟨t, ht, hval ▸ ⟨g, s₀, e, hs₀, hg, hs₀e, rfl⟩⟩
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
