-- Prove2me | solution 1 for ReciprocityTheory.Coh.CCA.retr_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:46:19.990654+00:00
-- url     : https://prove2.me/submissions/7c191f42-ed3f-4a06-b44d-d34256400750

import Definitions.Def_ReciprocityTheory_GroupCohomology_ContinuousContractNth
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
import Theorems.Thm_ReciprocityTheory_Coh_CCA_rep_mul

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
theorem _root_.solution (x : U) (g : G) : retr U ((x : G) * g) = x * retr U g := by
  apply Subtype.ext
  simp only [retr, rep_mul, Subgroup.coe_mul, mul_assoc]
end ReciprocityTheory.Coh.CCA
