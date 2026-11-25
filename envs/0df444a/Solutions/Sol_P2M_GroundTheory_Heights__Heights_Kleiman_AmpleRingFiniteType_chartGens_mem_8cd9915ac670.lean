-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_chartGens_mem_8cd9915ac670
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:10:07.493883+00:00
-- url     : https://prove2.me/submissions/62b353c0-3f61-419c-bc52-cc08d1ac9ab5

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
theorem _root_.solution (J : Chart x) : ∀ y ∈ chartGens J, y ∈ chartRing S x J := by
  classical
  intro y hy
  unfold chartGens at hy
  obtain ⟨⟨i, l⟩, hp, rfl⟩ := Finset.mem_image.mp (by convert hy)
  exact ⟨X i, X l, 1, X_mem_monos (Finset.mem_product.mp hp).2, isHomogeneous_X S i,
    isHomogeneous_X S l, by simp⟩
end GroundTheory.Heights₂.Heights.Kleiman.AmpleRingFiniteType
