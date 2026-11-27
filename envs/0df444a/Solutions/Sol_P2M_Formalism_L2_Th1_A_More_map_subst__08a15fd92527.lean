-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_A_More_map_subst__08a15fd92527
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:51:39.296314+00:00
-- url     : https://prove2.me/submissions/c6484c72-3c0c-4c2c-8caa-acd3870a7d2a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementM
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ChainRuleFormalGroupVar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.More
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
namespace Formalism.L2.Th1.A.More
theorem _root_.solution (φ : R →+* S) {s : R⟦X⟧} (hs : HasSubst s) (f : R⟦X⟧) :
    PowerSeries.map φ (f.subst s) = (PowerSeries.map φ f).subst (PowerSeries.map φ s) := by
  first
    | exact PowerSeries.map_subst hs φ f
    | exact PowerSeries.map_subst hs f
    | exact PowerSeries.map_subst φ hs f
    | exact (PowerSeries.subst_map hs φ f).symm
end Formalism.L2.Th1.A.More
