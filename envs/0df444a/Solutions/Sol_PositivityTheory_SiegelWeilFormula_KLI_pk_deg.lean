-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KLI.pk_deg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:14.975611+00:00
-- url     : https://prove2.me/submissions/f545b500-3448-4481-bd4c-d2d34bbcfc8a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KLI
namespace PositivityTheory.SiegelWeilFormula.KLI
theorem _root_.solution (b : ℂ) : ∀ k, (pk b k).natDegree ≤ k
  | 0 => by simp [pk]
  | 1 => by
    simp only [pk]
    exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
  | (k + 2) => by
    simp only [pk]
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine Polynomial.natDegree_mul_le.trans ?_
      have := solution b (k + 1)
      have := (Polynomial.natDegree_X_le (R := ℂ))
      omega
    · exact (Polynomial.natDegree_C_mul_le _ _).trans ((solution b k).trans (by omega))
end PositivityTheory.SiegelWeilFormula.KLI
