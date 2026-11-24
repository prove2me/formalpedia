-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CharacterRelations.eval_sumMono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:42.90429+00:00
-- url     : https://prove2.me/submissions/a2130938-94d4-4d49-a8dc-dd8f0e4ea74c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepChar
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.CharacterRelations
variable {A : Type*} [Ring A] [Algebra ℂ A]
set_option linter.unusedSectionVars false
namespace PositivityTheory.Rg.Cz.CharacterRelations
theorem _root_.solution (d : ℕ → A) (N : ℕ) (u : ℂ) :
    (∑ i ∈ Finset.range N, monomial i (d i)).eval (algebraMap ℂ A u) = ∑ i ∈ Finset.range N, u ^ i • d i := by
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_monomial, ← map_pow, Algebra.smul_def,
    Algebra.commutes]
end PositivityTheory.Rg.Cz.CharacterRelations
