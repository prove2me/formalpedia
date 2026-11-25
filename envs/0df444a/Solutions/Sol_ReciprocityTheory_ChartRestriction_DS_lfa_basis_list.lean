-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lfa_basis_list
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:23:52.135432+00:00
-- url     : https://prove2.me/submissions/39a831e3-95c1-467c-869b-e24c8df810c8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockA

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
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (S : Finset (Fin (n * n))) :
    fockBasis n S = ((List.ofFn fun i => finProdFinEquiv.symm (S.orderEmbOfFin rfl i)).map
      fun y => ExteriorAlgebra.ι ℂ (Pi.single y (1 : ℂ))).prod := by
  rw [fockBasis, ExteriorAlgebra.basis_apply_ofCard _ (rfl : S.card = S.card), ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply, List.map_ofFn]
  congr 2
  funext i
  simp [Set.powersetCard.ofFinEmbEquiv_symm_apply]
end ReciprocityTheory.ChartRestriction.DS
