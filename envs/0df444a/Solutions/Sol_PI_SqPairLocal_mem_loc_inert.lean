-- Prove2me | solution 1 for PI.SqPairLocal.mem_loc_inert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:26.096012+00:00
-- url     : https://prove2.me/submissions/bc629c8d-2ac1-41e0-b845-1a09cebe5f70

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnimodGenus
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsUnimodularOfIsSDG
import Theorems.Thm_PI_SqPairLocal_mem_hcompl_of_inert
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG PI.UG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PI.SqPairLocal
theorem _root_.solution {Q : Ideal (𝓞 E)} (hQ : Q.IsPrime) (hc : Q.comap (cj E) = Q) {N : ℕ}
    (L : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    y ∈ loc (K := E) Q L ↔ ∃ s : 𝓞 E, s ∉ Q ∧ s • y ∈ L := by
  simp [loc, locS, mem_hcompl_of_inert hQ hc]
end PI.SqPairLocal
