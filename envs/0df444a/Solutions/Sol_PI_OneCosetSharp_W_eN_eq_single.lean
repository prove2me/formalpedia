-- Prove2me | solution 1 for PI.OneCosetSharp.W.eN_eq_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:00:46.617972+00:00
-- url     : https://prove2.me/submissions/a8ade24b-8696-445a-9a7b-ef2e6865f49d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_Assemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W
open Loc LocE
namespace PI.OneCosetSharp.W
theorem _root_.solution {k : Type} [Field k] {N : ℕ} (i : ℕ) (hi : i < N) :
    eN k N i = Pi.single (⟨i, hi⟩ : Fin N) 1 := by
  ext l
  simp only [eN, Pi.single_apply, Fin.ext_iff]
end PI.OneCosetSharp.W
