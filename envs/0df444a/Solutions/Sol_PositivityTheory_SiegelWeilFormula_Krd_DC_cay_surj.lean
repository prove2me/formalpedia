-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Krd.DC.cay_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:57:33.901129+00:00
-- url     : https://prove2.me/submissions/c038352b-66da-4767-b1f0-164f9f8e5e22

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseCP
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseC
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_CP_cay_surj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Krd PositivityTheory.SiegelWeilFormula.Krd.DC
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PositivityTheory.SiegelWeilFormula.Krd.DC
theorem _root_.solution {J h : Matrix ι ι ℂ} (hh : InU J h) (hu : IsUnit (1 + h).det) :
    ∃ Y, InLie J Y ∧ IsUnit (1 - Y).det ∧ cay Y = h := by
  exact PositivityTheory.SiegelWeilFormula.Krd.CP.cay_surj hh hu
end PositivityTheory.SiegelWeilFormula.Krd.DC
