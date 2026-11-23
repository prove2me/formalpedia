-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InfKA.contDiff_lead
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:57.046686+00:00
-- url     : https://prove2.me/submissions/a2ae0189-2afa-4134-b042-4ba2d6199bf2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM

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
open ReciprocityTheory.ChartRestriction.DS.S7.InfKA
namespace ReciprocityTheory.ChartRestriction.DS.S7.InfKA
theorem _root_.solution (i : ℕ) : ContDiff ℂ 1 (fun z : Matrix (Fin n) (Fin n) ℂ => lead i z) := by
  have he : ∀ a b : Fin n, ContDiff ℂ 1 (fun z : Matrix (Fin n) (Fin n) ℂ => z a b) := by
    intro a b
    first
    | exact contDiff_apply_apply ℂ ℂ a b
    | exact contDiff_apply_apply a b
    | exact ((ContinuousLinearMap.proj b).comp (ContinuousLinearMap.proj a)).contDiff
    | fun_prop
  unfold lead
  by_cases h : i ≤ n
  · simp only [dif_pos h, Matrix.det_apply, Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul]
    exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun j _ => he _ _)
  · simp only [dif_neg h]
    exact contDiff_const
end ReciprocityTheory.ChartRestriction.DS.S7.InfKA
