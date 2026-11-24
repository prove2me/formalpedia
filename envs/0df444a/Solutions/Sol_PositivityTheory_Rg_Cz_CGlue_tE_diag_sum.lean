-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CGlue.tE_diag_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:50.060636+00:00
-- url     : https://prove2.me/submissions/a1c9c440-86e6-45b9-8123-bd80b8d1d3e4

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
variable {n : ℕ} {P : Type} [Fintype P] [DecidableEq P]
namespace PositivityTheory.Rg.Cz.CGlue
theorem _root_.solution (S : Finset P) (f : TV n ℂ P) :
    ∑ i, tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) i i f = (S.card : ℂ) • f := by
  funext I
  simp [tE, lift, eAt, Finset.sum_apply]
  rw [Finset.sum_comm]
  have key : ∀ p, ∑ c : Fin n, (if I p = c then (LinearMap.proj (Function.update I p c) : TV n ℂ P →ₗ[ℂ] ℂ) else 0) f =
      ∑ c : Fin n, if I p = c then f I else 0 := by
    intro p
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with h
    · subst h; simp
    · simp
  simp [key]
end PositivityTheory.Rg.Cz.CGlue
