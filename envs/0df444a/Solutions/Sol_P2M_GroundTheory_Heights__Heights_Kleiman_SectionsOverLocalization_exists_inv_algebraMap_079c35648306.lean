-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_inv_algebraMap_079c35648306
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:13:29.161965+00:00
-- url     : https://prove2.me/submissions/bba0b331-30a9-4666-b0a2-96b12e43d04a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulMemSecsTwistIdealSys

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
theorem _root_.solution {t : S} (ht : t ∉ 𝔪) : ∃ u : O, algebraMap O Ω u * algebraMap S Ω t = 1 := by
  obtain ⟨v, hv⟩ := IsLocalization.map_units O (⟨t, ht⟩ : 𝔪.primeCompl)
  refine ⟨(v⁻¹ : Oˣ), ?_⟩
  rw [IsScalarTower.algebraMap_apply S O Ω, ← map_mul]
  change algebraMap O Ω ((v⁻¹ : Oˣ) * algebraMap S O t) = 1
  rw [← hv, Units.inv_mul, map_one]
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
