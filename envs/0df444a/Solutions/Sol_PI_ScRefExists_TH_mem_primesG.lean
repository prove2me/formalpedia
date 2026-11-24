-- Prove2me | solution 1 for PI.ScRefExists.TH.mem_primesG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:35:08.081484+00:00
-- url     : https://prove2.me/submissions/386e4771-977f-4832-b0d3-419ce4356dea

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaSeriesExistence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open PI PI.ScRefExists PI.ScRefExists.TH
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.TH
theorem _root_.solution (g : ℕ) (hg : 1 ≤ g) (P : HeightOneSpectrum (𝓞 I.E)) :
    P ∈ primesG I g hg ↔ (g : 𝓞 I.E) ∈ P.asIdeal := by
  unfold primesG
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
end PI.ScRefExists.TH
