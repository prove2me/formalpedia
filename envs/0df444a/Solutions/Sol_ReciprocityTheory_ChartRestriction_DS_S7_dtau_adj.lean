-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.dtau_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:52:11.070658+00:00
-- url     : https://prove2.me/submissions/6fe34b5b-c822-4fc9-b466-43bbcc3254c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_block_decomp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dtau_skew

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
theorem _root_.solution (T : KType ε Λ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsBlock ε X) :
    ContinuousLinearMap.adjoint (T.dτ X) = T.dτ Xᴴ := by
  obtain ⟨A, B, hA, hB, hX1, hX2⟩ := block_decomp hX
  rw [hX2, hX1]
  simp [map_add, map_neg, map_smul, LinearIsometryEquiv.map_smulₛₗ, dtau_skew T hA, dtau_skew T hB,
    Complex.conj_I]
end ReciprocityTheory.ChartRestriction.DS.S7
