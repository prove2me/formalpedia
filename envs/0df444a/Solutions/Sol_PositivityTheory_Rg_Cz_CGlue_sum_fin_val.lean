-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CGlue.sum_fin_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:32:11.492905+00:00
-- url     : https://prove2.me/submissions/d0b3ab22-0bd4-4e72-8916-03154695a807

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_KTypeData
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CoefficientGluing_SumFinVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Formalism.REAL
open scoped TensorProduct
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CGlue
namespace PositivityTheory.Rg.Cz.CGlue
theorem _root_.solution (n : ℕ) : (∑ i : Fin n, ((i : ℕ) : ℝ)) * 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc, add_mul]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring
end PositivityTheory.Rg.Cz.CGlue
