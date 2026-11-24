-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Act.C4.Bq.NQ.apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:52.582369+00:00
-- url     : https://prove2.me/submissions/dc4daacf-2f20-4c89-8437-0aa2152a4805

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ParabolicBlockForms_UpperBlockRankOneUpdate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Act PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq
open Matrix
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
namespace PositivityTheory.SiegelWeilFormula.Act.C4.Bq
namespace NQ
theorem _root_.solution {x y : ι} {M : Matrix ι ι R} (hM : NQ x y M) {k l : ι} (h : l = x ∨ (l ≠ y ∧ k ≠ x)) :
    M k l = (1 : Matrix ι ι R) k l := by
  rcases h with rfl | ⟨hly, hkx⟩
  · have := hM.1 k; rwa [Matrix.sub_apply, sub_eq_zero] at this
  · by_cases hlx : l = x
    · subst hlx; have := hM.1 k; rwa [Matrix.sub_apply, sub_eq_zero] at this
    · have := hM.2 k l hlx hly hkx; rwa [Matrix.sub_apply, sub_eq_zero] at this
end NQ
end PositivityTheory.SiegelWeilFormula.Act.C4.Bq
