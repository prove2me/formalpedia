-- Prove2me | solution 1 for ReciprocityTheory.Coh.CCA.continuous_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:45:17.502568+00:00
-- url     : https://prove2.me/submissions/59d1a17a-7e3b-44f1-8ac4-178d0caa9f1e

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
theorem _root_.solution (hU : IsOpen (U : Set G)) : Continuous (rep U) := by
  rw [continuous_iff_continuousAt]
  intro g
  have hmem : (fun y => y * g⁻¹) ⁻¹' (U : Set G) ∈ nhds g := by
    apply (hU.preimage (continuous_mul_right g⁻¹)).mem_nhds
    simp [U.one_mem]
  apply (continuousAt_const (y := rep U g)).congr
  filter_upwards [hmem] with y hy
  have h1 : rep U ((⟨y * g⁻¹, hy⟩ : U) * g) = rep U g := rep_mul U ⟨y * g⁻¹, hy⟩ g
  simpa using h1.symm
end ReciprocityTheory.Coh.CCA
