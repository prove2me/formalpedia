-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InfKA.toMK_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:57.561592+00:00
-- url     : https://prove2.me/submissions/fd2714ca-3427-400e-98a8-9287219a913f

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
section
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace InfKA
private lemma toMK_conjTranspose_mul_self (k : KG ε) : (toMK k)ᴴ * toMK k = 1 := by
  have h : toM (k : UJ ε) ∈ Kset ε := k.2
  obtain ⟨hU, -⟩ := h
  first
  | exact Unitary.star_mul_self_of_mem hU
  | exact (Matrix.mem_unitaryGroup_iff').1 hU
  | exact hU.1
end InfKA
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
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
open ReciprocityTheory.ChartRestriction.DS.S7.InfKA
namespace ReciprocityTheory.ChartRestriction.DS.S7.InfKA
theorem _root_.solution (k : KG ε) : toMK k⁻¹ = (toMK k)ᴴ := by
  have hu : star (toMK k) * toMK k = 1 := toMK_conjTranspose_mul_self k
  have hv : toMK k * toMK k⁻¹ = 1 := by
    first
    | exact Units.mul_inv _
    | (simp only [toMK, toM]; simp)
    | (unfold toMK toM; simp)
    | (unfold toMK; simp)
  calc toMK k⁻¹ = (star (toMK k) * toMK k) * toMK k⁻¹ := by rw [hu, Matrix.one_mul]
    _ = star (toMK k) * (toMK k * toMK k⁻¹) := by rw [Matrix.mul_assoc]
    _ = (toMK k)ᴴ := by rw [hv, Matrix.mul_one]; rfl
end ReciprocityTheory.ChartRestriction.DS.S7.InfKA
