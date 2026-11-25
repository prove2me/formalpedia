-- Prove2me | solution 1 for PI.StabSplit.FixW.isometry_fix_flagAnisotropicVector_of_fix_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:37:34.201166+00:00
-- url     : https://prove2.me/submissions/7ef35b5d-4985-4882-9d38-b5ea4ec03c90

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_FixSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.StabSplit PI.StabSplit.FixW
namespace PI.StabSplit.FixW
theorem _root_.solution {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ FixSet k r z) :
    g *ᵥ z = z := by
  have h := hg.2 (Fin.last r)
  simpa [fvec] using h
end PI.StabSplit.FixW
