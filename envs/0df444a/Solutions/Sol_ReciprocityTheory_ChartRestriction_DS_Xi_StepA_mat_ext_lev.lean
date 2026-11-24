-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.mat_ext_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:40:59.468321+00:00
-- url     : https://prove2.me/submissions/c5958a6b-45d1-41f6-87a1-580b6128d6b5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DetEqMulMinorOfColZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RankOneLeviComm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_last
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_mp
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_zero_pos



set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution {A B : Mat k (1 + r')} (h0 : A *ᵥ e0 k r' = B *ᵥ e0 k r')
    (h1 : A *ᵥ es0 k r' = B *ᵥ es0 k r') (h2 : ∀ v, A *ᵥ liftVec k 1 r' v = B *ᵥ liftVec k 1 r' v) : A = B := by
  have key : ∀ q : Fin (2 * (1 + r') + k + 1), A *ᵥ Pi.single q 1 = B *ᵥ Pi.single q 1 := by
    intro q
    by_cases hq0 : q.val = 0
    · have he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) = e0 k r' := by
        have hq : q = eI k (1 + r') (a0 r') := Fin.ext (by simp [eI, a0, hq0])
        rw [hq]
        rfl
      rw [he, h0]
    by_cases hql : q.val = 2 * (1 + r') + k
    · have he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) = es0 k r' := by
        have hq : q = esI k (1 + r') (a0 r') := Fin.ext (by simp [esI, a0, hql])
        rw [hq]
        rfl
      rw [he, h1]
    · have he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) =
          liftVec k 1 r' (Pi.single ⟨q.val - 1, by omega⟩ 1) := by
        funext p
        simp only [liftVec, Pi.single_apply, Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [he, h2]
  ext p q
  have h := congrFun (key q) p
  simpa [Matrix.mulVec_single_one, Matrix.transpose_apply] using h
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
