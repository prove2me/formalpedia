-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FlagGramNonneg.cT_star_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:49.368838+00:00
-- url     : https://prove2.me/submissions/ab96bddb-1116-4f14-b6dd-dad38a48e658

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_HasSignatureExistsNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PI.FlagGramNonneg
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg
namespace PI.UnitaryGroupMassFormula.FlagGramNonneg
theorem _root_.solution {m n : Type} (M : Matrix m n ℂ) : cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [cT, Matrix.conjTranspose_apply]
end PI.UnitaryGroupMassFormula.FlagGramNonneg
