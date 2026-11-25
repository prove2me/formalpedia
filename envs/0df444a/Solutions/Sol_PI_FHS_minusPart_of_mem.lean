-- Prove2me | solution 1 for PI.FHS.minusPart_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:07:32.178818+00:00
-- url     : https://prove2.me/submissions/d27b8577-1c19-4566-9a9a-37f77931075e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_ConjTransposeOneKronecker
import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_MinusPartOfMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix FockH1Action
open PI PI.FHS
variable {σ : Type*}
namespace PI.FHS
theorem _root_.solution {A : Module.End ℂ (MvPolynomial σ ℂ)} {d : ℕ} {Q : MvPolynomial σ ℂ}
    (hQ : Q ∈ homog σ (d + 2)) : minusPart A Q = homogeneousComponent d (A Q) := by
  unfold minusPart
  rw [finsum_eq_single _ d]
  · rw [homogeneousComponent_of_mem hQ, if_pos rfl]
  · intro e he
    rw [homogeneousComponent_of_mem hQ, if_neg (by omega), map_zero, map_zero]
end PI.FHS
