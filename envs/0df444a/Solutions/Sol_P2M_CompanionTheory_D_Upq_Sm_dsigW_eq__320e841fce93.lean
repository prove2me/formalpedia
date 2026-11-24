-- Prove2me | solution 1 for P2M_CompanionTheory_D_Upq_Sm_dsigW_eq__320e841fce93
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:54:01.271821+00:00
-- url     : https://prove2.me/submissions/4b71b0ea-b3fd-4d85-b2d6-e0f27dba1d4c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LowCyc
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LowSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI.UpqRep
namespace CompanionTheory.D.Upq.Sm
theorem _root_.solution {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat (2 * r + k + 1) → (H →L[ℂ] H)) :
    ∀ (W : List (Mat (2 * r + k + 1))) (v : H), dsigW (k := k) (r := r) σ W v = dsW σ W v
  | [], _ => rfl
  | X :: W, v => by
    change dsig σ X (dsigW σ W v) = ds σ X (dsW σ W v)
    rw [solution σ W v]; rfl
end CompanionTheory.D.Upq.Sm
