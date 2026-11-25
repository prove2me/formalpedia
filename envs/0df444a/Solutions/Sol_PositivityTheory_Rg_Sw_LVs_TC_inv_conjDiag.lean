-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.inv_conjDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:46:24.98675+00:00
-- url     : https://prove2.me/submissions/4f3967a9-b30c-4be2-8870-e51680bed667

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatC
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_prod_conjDiag

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
theorem _root_.solution (d1 d2 : Fin n → ℂ) (h1 : ∀ a, d1 a ≠ 0) (h2 : ∀ a, d2 a ≠ 0) :
    (Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n)⁻¹ =
      Cm n * fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) * CmI n := by
  exact Matrix.inv_eq_right_inv (prod_conjDiag d1 d2 h1 h2)
end PositivityTheory.Rg.Sw.LVs.TC
