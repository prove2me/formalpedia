-- Prove2me | solution 1 for PI.UG.W.unimodLocal_of_locDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:32:46.559899+00:00
-- url     : https://prove2.me/submissions/0158d90c-c340-4e63-b15a-0745d03bf57d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_StdLatEqSpan
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_UnimodLocalOfLocDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UG PI.UG.W
namespace PI.UG.W
theorem _root_.solution (hLD : Formalism.HermitianLatticesTheory.LocDual) : UnimodLocal := by
  intro E _ _ _ n N hN hU p hp
  have hsymm : (hStd E n).IsSymm := by
    first
      | (refine ⟨fun x y => ?_⟩
         simp [hStd, map_sum, starRingEnd_apply, star_mul', mul_comm])
      | (intro x y
         simp [hStd, map_sum, starRingEnd_apply, star_mul', mul_comm])
  have hstar : ∀ r : 𝓞 E, star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) := by
    intro r
    exact ⟨RingOfIntegers.mapRingHom (starRingEnd E) r, rfl⟩
  have hfg : N.FG := hN.fg
  have key := (hLD (𝓞 E) E (Sp E n) (hStd E n) hsymm hstar N hfg).2
  exact key.mp hU p hp
end PI.UG.W
