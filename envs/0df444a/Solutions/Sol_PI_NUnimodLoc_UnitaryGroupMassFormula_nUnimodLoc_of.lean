-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.nUnimodLoc_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:52:06.670966+00:00
-- url     : https://prove2.me/submissions/262bbc3f-7923-4fb0-90b9-ceecc5cf2781

import Definitions.Def_Formalism_PeriodIntegrals_NUnimodLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_NonstandardUnimodularLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_nonstandard_unimodular_lattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.NUnimodLoc PI.NUnimodLoc.UnitaryGroupMassFormula
open PI PI.QuotSetU
namespace PI.NUnimodLoc.UnitaryGroupMassFormula
theorem _root_.solution (hF : FrameConj) (hT : Transfer) : NUnimodLoc := by
  intro k r ε e f wf z0 z c hfr hc hz μ hμ hne hsupp hleft
  obtain ⟨P, Q, hQP, hPQ, hiff⟩ := hF k r ε e f wf z0 z c hfr hc hz
  exact hT (2 * r + k + 1) ε {g | InN ε e z g} (Nset k r) P Q hQP hPQ (fun g => hiff g)
    (nonstandard_unimodular_lattice k r) μ hμ hne hsupp hleft
end PI.NUnimodLoc.UnitaryGroupMassFormula
