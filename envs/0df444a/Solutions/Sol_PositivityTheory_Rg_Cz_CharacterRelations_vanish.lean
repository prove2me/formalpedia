-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CharacterRelations.vanish
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:44.605061+00:00
-- url     : https://prove2.me/submissions/81dd0346-7b9e-4602-93a0-823d361aa632

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
theorem _root_.solution (D : A[X]) (a : ℂ) (h : ∀ u : ℂ, u ≠ a → D.eval (algebraMap ℂ A u) = 0) : D = 0 := by
  ext i
  rw [Polynomial.coeff_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (D.coeff i)).1 (fun φ => ?_)
  let q : ℂ[X] := ∑ j ∈ Finset.range (D.natDegree + 1), monomial j (φ (D.coeff j))
  have hq : ∀ u : ℂ, u ≠ a → q.eval u = 0 := by
    intro u hu
    have e := congrArg φ (h u hu)
    rw [Polynomial.eval_eq_sum_range, map_zero, map_sum] at e
    simp only [q, Polynomial.eval_finset_sum, Polynomial.eval_monomial]
    rw [← e]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have q0 : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := {a}ᶜ) (fun u hu => hq u hu) ?_
    exact (Set.finite_singleton a).infinite_compl
  by_cases hi : i < D.natDegree + 1
  · have e := congrArg (fun p => p.coeff i) q0
    simpa [q, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, hi] using e
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
end PositivityTheory.Rg.Cz.CharacterRelations
