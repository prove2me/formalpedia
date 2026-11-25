-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Krd.DC.scalar_avoid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:21.929878+00:00
-- url     : https://prove2.me/submissions/b4223343-4858-4c28-83cf-d0b7663dbcea

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseCP
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseC
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_CP_scalar_avoid


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
theorem _root_.solution {J h : Matrix ι ι ℂ} (hh : InU J h) {V : Set (Matrix ι ι ℂ)} (hV : IsOpen V) (hhV : h ∈ V) :
    ∃ μ : ℂ, star μ * μ = 1 ∧ μ • h ∈ V ∧ IsUnit (1 + μ • h).det := by
  exact PositivityTheory.SiegelWeilFormula.Krd.CP.scalar_avoid hh hV hhV
end PositivityTheory.SiegelWeilFormula.Krd.DC
