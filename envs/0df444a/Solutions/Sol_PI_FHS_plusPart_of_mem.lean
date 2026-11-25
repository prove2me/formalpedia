-- Prove2me | solution 1 for PI.FHS.plusPart_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:07:07.338171+00:00
-- url     : https://prove2.me/submissions/2f1b7430-7dec-4157-8378-6692adf755bd

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
theorem _root_.solution {A : Module.End ℂ (MvPolynomial σ ℂ)} {d : ℕ} {P : MvPolynomial σ ℂ}
    (hP : P ∈ homog σ d) : plusPart A P = homogeneousComponent (d + 2) (A P) := by
  unfold plusPart
  rw [finsum_eq_single _ d]
  · rw [homogeneousComponent_of_mem hP, if_pos rfl]
  · intro e he
    rw [homogeneousComponent_of_mem hP, if_neg he, map_zero, map_zero]
end PI.FHS
