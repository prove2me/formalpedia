-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.factorAd_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:40.927206+00:00
-- url     : https://prove2.me/submissions/cac34c1e-35f0-4feb-b3d8-d46f8c5c3999

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep

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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (k : ℕ) (i : Fin k) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    (factorAd (M := M) k i a b F) κ =
      (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) -
        (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) := by
  change ((if (κ i).1 = a then coord k (Function.update κ i (b, (κ i).2)) else 0) -
      (if (κ i).2 = b then coord k (Function.update κ i ((κ i).1, a)) else 0) :
      Big n k M →ₗ[ℂ] M) F = _
  rw [LinearMap.sub_apply]
  split_ifs <;> rfl
end ReciprocityTheory.ChartRestriction.DS
