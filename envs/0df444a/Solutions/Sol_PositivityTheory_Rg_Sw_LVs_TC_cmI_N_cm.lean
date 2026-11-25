-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.cmI_N_cm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:49:01.295307+00:00
-- url     : https://prove2.me/submissions/fd768d5c-6038-47f4-bd6e-189b6a48160b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution (E : Matrix (Fin n) (Fin n) ℂ) :
    CmI n * fromBlocks 0 E 0 0 * Cm n = ((2 * Complex.I)⁻¹ : ℂ) • fromBlocks E E (-E) (-E) := by
  rw [CmI, Cm, Matrix.smul_mul, Matrix.smul_mul, fromBlocks_multiply, fromBlocks_multiply]
  congr 1
  simp
  done
end PositivityTheory.Rg.Sw.LVs.TC
