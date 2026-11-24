-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.smul_mem_AT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:41.986284+00:00
-- url     : https://prove2.me/submissions/febdd717-21d3-4beb-a588-6f210fe566b3

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (c : ℂ) {Q : Fm n} (hQ : Q ∈ AT n) : c • Q ∈ AT n := by
  rw [← algebraMap_smul (Polynomial ℂ) c Q]
  exact Subalgebra.smul_mem _ hQ _
end PositivityTheory.Rg.Sw.SP
