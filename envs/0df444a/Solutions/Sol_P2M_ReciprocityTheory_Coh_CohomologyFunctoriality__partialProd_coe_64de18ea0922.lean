-- Prove2me | solution 1 for P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__partialProd_coe_64de18ea0922
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:59:31.167944+00:00
-- url     : https://prove2.me/submissions/95bafb07-b035-4f9b-9075-fc8f488eeff4

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_PartialProdCoe

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
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.CohomologyFunctoriality₂
theorem _root_.solution {N : Subgroup G} {n : ℕ} (g : Fin n → N) (j : Fin (n + 1)) :
    Fin.partialProd (fun i => (g i : G)) j = ((Fin.partialProd g j : N) : G) := by
  induction j using Fin.induction with
  | zero => simp [Fin.partialProd_zero]
  | succ j ih => simp [Fin.partialProd_succ, ih]
end ReciprocityTheory.Coh.CohomologyFunctoriality₂
