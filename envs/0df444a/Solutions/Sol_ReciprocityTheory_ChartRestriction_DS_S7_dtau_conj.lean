-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.dtau_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:56:27.155795+00:00
-- url     : https://prove2.me/submissions/108ed15a-8e5b-4170-a400-50c844361478

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_block_decomp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dtau_conj_inK

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
theorem _root_.solution (T : KType ε Λ) (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsBlock ε X) :
    T.op k * T.dτ X * T.op k⁻¹ = T.dτ (toMK k * X * toMK k⁻¹) := by
  obtain ⟨A, B, hA, hB, hX1, -⟩ := block_decomp hX
  subst hX1
  have e1 : toMK k * (A + Complex.I • B) * toMK k⁻¹ =
      toMK k * A * toMK k⁻¹ + Complex.I • (toMK k * B * toMK k⁻¹) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [e1, map_add, map_smul, map_add, map_smul, ← dtau_conj_inK T k hA, ← dtau_conj_inK T k hB,
    mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
end ReciprocityTheory.ChartRestriction.DS.S7
