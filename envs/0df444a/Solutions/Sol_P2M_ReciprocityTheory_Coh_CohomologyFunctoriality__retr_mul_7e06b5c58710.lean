-- Prove2me | solution 1 for P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_mul_7e06b5c58710
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:09.870558+00:00
-- url     : https://prove2.me/submissions/00891f4b-6248-4f39-83b5-91c28cb62785

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_PartialProdCoe
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__rep_mul_d1c6e7d42e8b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Coh.CohomologyFunctoriality₂
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
namespace ReciprocityTheory.Coh.CohomologyFunctoriality₂
theorem _root_.solution (x : U) (g : G) : retr U ((x : G) * g) = x * retr U g := by
  apply Subtype.ext
  simp only [retr, rep_mul, Subgroup.coe_mul, mul_assoc]
end ReciprocityTheory.Coh.CohomologyFunctoriality₂
