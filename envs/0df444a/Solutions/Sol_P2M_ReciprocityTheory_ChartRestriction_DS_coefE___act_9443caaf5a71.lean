-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_coefE___act_9443caaf5a71
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:01:10.612323+00:00
-- url     : https://prove2.me/submissions/aa7bd7c4-b323-4502-ad02-da294698182e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefDTensActPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefETensGrpMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open scoped Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (dual : Bool) {V' : Submodule ℂ D} {ι : D →ₗ[ℂ] (Fin n → D)}
    (hιE : ∀ a b, ∀ x ∈ genSub E V', ι (E a b x) = tensF dual E a b (ι x))
    (X : Matrix (Fin n) (Fin n) ℂ) {v : D} (hv : v ∈ genSub E V') :
    ι (actM E X v) = actM (tensF dual E) X (ι v) := by
  simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    hιE _ _ v hv]
end ReciprocityTheory.ChartRestriction.DS
