-- Prove2me | solution 1 for ReciprocityTheory.Coh.CCA.rep_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:50.493694+00:00
-- url     : https://prove2.me/submissions/7df391f4-2ab2-4f8d-9627-4cfeabdfb451

import Definitions.Def_ReciprocityTheory_GroupCohomology_ContinuousContractNth
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
namespace ReciprocityTheory.Coh.CCA
theorem _root_.solution (x : U) (g : G) : rep U ((x : G) * g) = rep U g := by
  unfold rep
  congr 1
  rw [mkR_eq]
  simpa [mul_inv_rev] using U.inv_mem x.2
end ReciprocityTheory.Coh.CCA
