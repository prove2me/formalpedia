-- Prove2me | solution 1 for P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__continuous_rep_745e730e9170
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:10.221812+00:00
-- url     : https://prove2.me/submissions/6273e164-3eb3-49e7-b090-99594f33c047

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
theorem _root_.solution (hU : IsOpen (U : Set G)) : Continuous (rep U) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hn : (fun y => y * x⁻¹) ⁻¹' (U : Set G) ∈ nhds x := by
    refine (hU.preimage (continuous_mul_const _)).mem_nhds ?_
    simp [U.one_mem]
  refine (continuousAt_const (y := rep U x)).congr ?_
  filter_upwards [hn] with y hy
  have : y = ((⟨y * x⁻¹, hy⟩ : U) : G) * x := by simp
  rw [this, rep_mul]
end ReciprocityTheory.Coh.CohomologyFunctoriality₂
