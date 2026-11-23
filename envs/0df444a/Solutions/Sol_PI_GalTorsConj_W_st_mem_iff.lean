-- Prove2me | solution 1 for PI.GalTorsConj.W.st_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:59.694294+00:00
-- url     : https://prove2.me/submissions/099b298f-8f7d-48bf-8abd-ae2a2b149b47

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_StAddRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Formalism.L2.Th1.F
variable {L L' : PeriodPair} {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ}
namespace PI.GalTorsConj.W
theorem _root_.solution {t t' : ℂ} (h : St L L' M ρ t t') : t ∈ L.lattice ↔ t' ∈ L'.lattice := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, _⟩
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
end PI.GalTorsConj.W
