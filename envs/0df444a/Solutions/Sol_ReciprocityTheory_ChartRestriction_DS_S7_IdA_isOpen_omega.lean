-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.IdA.isOpen_omega
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T03:18:58.064952+00:00
-- url     : https://prove2.me/submissions/38e7e0fb-71cf-49dd-a6f6-d31432313d95

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IdThmA
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
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
open ReciprocityTheory.ChartRestriction.DS.S7.IdA

theorem ReciprocityTheory.ChartRestriction.DS.S7.IdA.isOpen_omega : IsOpen (OmegaSet n) := by
  have hc : ∀ i : Fin n, Continuous
      (fun z : Matrix (Fin n) (Fin n) ℂ => ReciprocityTheory.ChartRestriction.DS.S7.lead ((i : ℕ) + 1) z) := by
    intro i
    unfold ReciprocityTheory.ChartRestriction.DS.S7.lead
    split_ifs with h
    · exact (continuous_id.matrix_submatrix _ _).matrix_det
    · exact continuous_const
  have hset : ReciprocityTheory.ChartRestriction.DS.S7.OmegaSet n =
      ⋂ i : Fin n, {z | ReciprocityTheory.ChartRestriction.DS.S7.lead ((i : ℕ) + 1) z ≠ 0} := by
    ext z; simp [ReciprocityTheory.ChartRestriction.DS.S7.OmegaSet]
  rw [hset]
  exact isOpen_iInter_of_finite fun i => isOpen_ne_fun (hc i) continuous_const


end

theorem solution {n : ℕ} : IsOpen (ReciprocityTheory.ChartRestriction.DS.S7.OmegaSet n) :=
  ReciprocityTheory.ChartRestriction.DS.S7.IdA.isOpen_omega
