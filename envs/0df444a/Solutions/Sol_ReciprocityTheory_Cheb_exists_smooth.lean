-- Prove2me | solution 1 for ReciprocityTheory.Cheb.exists_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:39.017803+00:00
-- url     : https://prove2.me/submissions/997a5391-42e9-4397-91c5-c7458fcf382b

import Definitions.Def_ReciprocityTheory_Chebotarev_EulerFin
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {E : Type} [Field E] [NumberField E] (a : NZIdeal E) : ∃ S : Finset (Prm E), Smooth S a.1 := by
  have hfin := Ideal.finite_factors (R := 𝓞 E) (I := a.1) a.2
  exact ⟨hfin.toFinset, fun q hq => hfin.mem_toFinset.mpr hq⟩
end ReciprocityTheory.Cheb
