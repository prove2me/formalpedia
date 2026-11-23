-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InfKA.conj_mem_omega
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:23.644333+00:00
-- url     : https://prove2.me/submissions/e68010cd-436f-4db2-8168-87567c430ff3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_toMK_inv_eq
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
theorem _root_.solution {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (k : KG ε) :
    toMK k⁻¹ * x * toMK k ∈ OmegaSet n := by
  rw [toMK_inv_eq]
  have hinj : Function.Injective (toMK k).mulVec := fun v w h => by
    have h2 := congrArg (toMK k)ᴴ.mulVec h
    simpa [Matrix.mulVec_mulVec, toMK_conjTranspose_mul_self] using h2
  have hP : ((toMK k)ᴴ * x * toMK k).PosDef := hx.conjTranspose_mul_mul_same hinj
  show ∀ i : Fin n, lead ((i : ℕ) + 1) ((toMK k)ᴴ * x * toMK k) ≠ 0
  intro i
  unfold lead
  rw [dif_pos (show (i : ℕ) + 1 ≤ n from i.isLt)]
  first
  | exact (hP.submatrix (Fin.castLE_injective _)).det_pos.ne'
  | exact (hP.submatrix (Fin.castLEEmb (show (i : ℕ) + 1 ≤ n from i.isLt))).det_pos.ne'
  | exact (hP.submatrix _ (Fin.castLE_injective _)).det_pos.ne'
end ReciprocityTheory.ChartRestriction.DS.S7.InfKA
