-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.psiM_kexp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:42.701525+00:00
-- url     : https://prove2.me/submissions/98a49b0e-0980-4a20-be99-9edb06deb68f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousConjProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ToMKMulInv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_polar_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    PsiM T μ (toMK k * NormedSpace.exp X) = T.op k * psM T μ (NormedSpace.exp X) := by
  have h : ∃ (k' : KG ε) (X' : Matrix (Fin n) (Fin n) ℂ), inP ε X' ∧
      toMK k * NormedSpace.exp X = toMK k' * NormedSpace.exp X' := ⟨k, X, hX, rfl⟩
  obtain ⟨hk, hXX⟩ := polar_unique hX h.choose_spec.choose_spec.1 h.choose_spec.choose_spec.2
  rw [PsiM, dif_pos h, ← hXX, ← hk]
end ReciprocityTheory.ChartRestriction.DS.S7
