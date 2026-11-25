-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.polar_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:03.452876+00:00
-- url     : https://prove2.me/submissions/eca3592d-1310-419d-96f0-39fa286376ee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_isHermitian_of_mem_noncompactPart__f516412af8b5
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_kexp_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_exp_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_exp_mul_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_half


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
variable {ε : Fin n → Bool}
open PolarDecomposition
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {k k' : KG ε} {X X' : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (hX' : inP ε X')
    (h : toMK k * NormedSpace.exp X = toMK k' * NormedSpace.exp X') : k = k' ∧ X = X' := by
  have hH := isHermitian_of_mem_noncompactPart' hX
  have hH' := isHermitian_of_mem_noncompactPart' hX'
  have hXX : X + X = X' + X' := by
    refine polar_exp_inj (by rw [conjTranspose_add, hH]) (by rw [conjTranspose_add, hH']) ?_
    rw [← kexp_sq k hH, ← kexp_sq k' hH', h]
  have hXe : X = X' := polar_half hXX
  subst hXe
  refine ⟨?_, rfl⟩
  have hm : toMK k = toMK k' := by
    have := congrArg (· * NormedSpace.exp (-X)) h
    simp only [Matrix.mul_assoc, polar_exp_mul_neg, Matrix.mul_one] at this
    exact this
  exact Subtype.ext (Subtype.ext (Units.ext hm))
end ReciprocityTheory.ChartRestriction.DS.S7
