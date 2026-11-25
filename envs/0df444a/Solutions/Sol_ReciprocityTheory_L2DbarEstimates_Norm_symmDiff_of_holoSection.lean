-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Norm.symmDiff_of_holoSection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:19:22.503802+00:00
-- url     : https://prove2.me/submissions/a7adf1a1-3fa7-48cf-8b9f-4adf5f553540

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_Sheets
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_HoloSectionStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_SymmDiff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Norm_sheets


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Norm
open Filter Topology Asymptotics
universe u
namespace ReciprocityTheory.L2DbarEstimates.Norm
theorem _root_.solution (hsec : holoSectionStatement.{u}) : symmDiffStatement.{u} := by
  intro n M _ z U u hcov hU hfinU hholo k w hw
  have hloc : IsLocalHomeomorph z := by
    rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
    have := hcov.isLocalHomeomorphOn
    rwa [Set.preimage_eq_univ_iff.mpr (by rintro _ ⟨x, rfl⟩; exact hU x)] at this
  obtain ⟨W, d, s, hW, hwW, hcont, hzs, hvals⟩ := sheets n M z U u hcov w hw (hfinU w hw)
  have hWn : W ∈ 𝓝 w := hW.mem_nhds hwW
  have hdiff : ∀ i, DifferentiableAt ℂ (fun v => u (s i v)) w := fun i =>
    hsec n M z u hloc hholo (s i) w ((hcont i).continuousAt hWn)
      (Filter.eventually_of_mem hWn (hzs i))
  have heq : (fun v => ∑ t ∈ (Finset.univ : Finset (Fin d)).powersetCard k, ∏ i ∈ t, u (s i v))
      =ᶠ[𝓝 w] fiberSymm n z u k := by
    filter_upwards [hWn] with v hv
    rw [fiberSymm, hvals v hv, Finset.esymm_map_val]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq.symm
  have hprod : ∀ t : Finset (Fin d), DifferentiableAt ℂ (fun v => ∏ i ∈ t, u (s i v)) w := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hdiff a).mul ih
  exact DifferentiableAt.fun_sum fun t _ => hprod t
end ReciprocityTheory.L2DbarEstimates.Norm
