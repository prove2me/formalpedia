-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_coefB___casimirK_9818b3c5805b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:23.993636+00:00
-- url     : https://prove2.me/submissions/aecfa4ee-ddcd-4368-8291-064030f2d078

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefAInnerEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefBTensSubKStable

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (dual : Bool) {S' : Submodule ℂ D} {ι : D →ₗ[ℂ] (Fin n → D)}
    (hS' : ∀ a b, ∀ v ∈ S', E a b v ∈ S')
    (hι : ∀ a b, ∀ x ∈ S', ι (E a b x) = tensF dual E a b (ι x)) {y : D} (hy : y ∈ S') :
    ι (casimirK ε E y) = casimirK ε (tensF dual E) (ι y) := by
  simp only [casimirK, LinearMap.sum_apply, map_sum, Module.End.mul_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hι a b _ (hS' b a y hy), hι b a y hy]
end ReciprocityTheory.ChartRestriction.DS
