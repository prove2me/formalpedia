-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_overDen_apply_c50c6731e4a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:29:21.655132+00:00
-- url     : https://prove2.me/submissions/7548482f-bcb9-4ef6-9613-fe99db499b0b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeDecompSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHFreeDecomp

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.KHFreeDecomp
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
namespace GroundTheory.Heights₂.Heights.Kleiman.KHFreeDecomp
theorem _root_.solution (T : Submonoid (MRingOver S ι)) (t : T) (m : M) :
    overDen T t m = LocalizedModule.mk m t := rfl
end GroundTheory.Heights₂.Heights.Kleiman.KHFreeDecomp
