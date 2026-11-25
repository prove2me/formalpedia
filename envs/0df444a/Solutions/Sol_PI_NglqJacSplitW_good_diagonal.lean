-- Prove2me | solution 1 for PI.NglqJacSplitW.good_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:09:53.892304+00:00
-- url     : https://prove2.me/submissions/3278de86-b94f-4cfd-abc0-3754d10f0ca1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_FactorOneOfDiscrete
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_GoodTransvection
import Theorems.Thm_PI_NglqJacSplitW_chiM_diagOne
import Theorems.Thm_PI_NglqJacSplitW_good_mul
import Theorems.Thm_PI_NglqJacSplitW_good_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal
open PI PI.NglqJacSplitW
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.NglqJacSplitW
theorem _root_.solution (hD : DiagOne) (D : ι → F) (hD0 : ∀ i, D i ≠ 0) : Good (diagonal D) := by
  classical
  have key : ∀ s : Finset ι, ∀ D : ι → F, (∀ i, D i ≠ 0) → (∀ i ∉ s, D i = 1) → Good (diagonal D) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro D _ h1
      have : D = 1 := funext fun i => h1 i (Finset.notMem_empty i)
      rw [this, show diagonal (1 : ι → F) = 1 from diagonal_one]
      exact good_one
    | @insert i s hi ih =>
      intro D hD0 h1
      have hsplit : diagonal D = diagonal (Function.update D i 1) * diagonal (Function.update (1 : ι → F) i (D i)) := by
        rw [diagonal_mul_diagonal]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj
          simp
        · simp [Function.update_of_ne hj]
      have hdet1 : (diagonal (Function.update (1 : ι → F) i (D i))).det = D i := by
        rw [det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
        simp
      have hne : ∀ j, Function.update D i 1 j ≠ 0 := fun j => by
        by_cases hj : j = i
        · subst hj
          simp
        · rw [Function.update_of_ne hj]
          exact hD0 j
      rw [hsplit]
      refine good_mul ?_ (by rw [hdet1]; exact hD0 i) (ih _ hne fun j hj => ?_) fun h => ?_
      · rw [det_diagonal]
        exact Finset.prod_ne_zero_iff.mpr fun j _ => hne j
      · by_cases hji : j = i
        · subst hji
          simp
        · rw [Function.update_of_ne hji]
          exact h1 j (by simp [hji, hj])
      · rw [chiM_diagOne hD i (D i) (hD0 i) h, hdet1]
  exact key Finset.univ D hD0 fun i hi => absurd (Finset.mem_univ i) hi
end PI.NglqJacSplitW
