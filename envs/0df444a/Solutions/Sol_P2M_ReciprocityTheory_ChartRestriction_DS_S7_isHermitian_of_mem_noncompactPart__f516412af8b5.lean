-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_S7_isHermitian_of_mem_noncompactPart__f516412af8b5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:56.962371+00:00
-- url     : https://prove2.me/submissions/56e6bc68-e1e2-4d52-9091-90f49d885fb1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool}
open PolarDecomposition
private lemma Jm_mul_self_eq_one' : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num
end ReciprocityTheory.ChartRestriction.DS.S7
end
end

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool}
open PolarDecomposition
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : Xᴴ = X := by
  obtain ⟨hG, hXJ⟩ := hX
  have hJ := Jm_mul_self_eq_one' (ε := ε)
  have h1 : Xᴴ * Jm ε = X * Jm ε := by
    rw [hXJ]
    unfold inG at hG
    exact eq_neg_of_add_eq_zero_left hG
  calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, hJ, mul_one]
    _ = X * Jm ε * Jm ε := by rw [h1]
    _ = X := by rw [mul_assoc, hJ, mul_one]
end ReciprocityTheory.ChartRestriction.DS.S7
