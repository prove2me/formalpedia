-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CGlue.sum_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:41:03.859404+00:00
-- url     : https://prove2.me/submissions/7198860c-edaa-48db-90a2-27f630d9435d

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
theorem _root_.solution (n : ℕ) (s : ℤ) (ν : Fin n → ℕ) (l : Fin n → ℤ) (w : Equiv.Perm (Fin n))
    (h : ∀ i, s - l (w i) = (ν i : ℤ) + (i : ℕ)) :
    ∑ k, ((l k : ℝ) + (k : ℕ)) = n * s - ∑ i, (ν i : ℝ) := by
  have hl : ∀ i, (l (w i) : ℝ) = s - ν i - (i : ℕ) := by
    intro i
    have := congrArg (Int.cast : ℤ → ℝ) (h i)
    push_cast at this
    linarith
  rw [Finset.sum_add_distrib, ← Equiv.sum_comp w (fun k => (l k : ℝ))]
  simp only [hl, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring
end PositivityTheory.Rg.Cz.CGlue
