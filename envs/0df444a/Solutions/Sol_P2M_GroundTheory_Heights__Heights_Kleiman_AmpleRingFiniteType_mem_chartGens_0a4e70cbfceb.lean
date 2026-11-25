-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_mem_chartGens_0a4e70cbfceb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:10:11.979206+00:00
-- url     : https://prove2.me/submissions/d6aff533-06db-40bc-bed6-5981e32899fa

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
theorem _root_.solution {J : Chart x} (i : Fin (N + 1)) {l : Fin (N + 1)} (hl : l ∈ J.1) :
    x i / x l ∈ chartGens J := by
  classical
  unfold chartGens
  convert Finset.mem_image.mpr ⟨(i, l), Finset.mem_product.mpr ⟨Finset.mem_univ _, hl⟩, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman.AmpleRingFiniteType
