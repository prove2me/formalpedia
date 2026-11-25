-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_eq_sing_332db549bcef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:19:15.238559+00:00
-- url     : https://prove2.me/submissions/eff75e64-def2-4574-b42c-e2341c0bd345

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrLenRestrict

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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type w} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
theorem _root_.solution (I : Cech.Idx (support x) 0) : ∃ (a : Fin (N + 1)) (ha : a ∈ support x), I = sing ha := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp I.2
  have hmem : a ∈ support x := I.1.2.2 (by rw [ha]; exact Finset.mem_singleton_self a)
  exact ⟨a, hmem, Subtype.ext (Subtype.ext ha)⟩
end GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
