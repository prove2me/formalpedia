-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjFullRankDense_of_found_ede29b385614
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:08:53.003411+00:00
-- url     : https://prove2.me/submissions/b4aab9e6-712b-44c8-ba73-a22717236e90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularClosureOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjFullRankMeetsRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjFullRankDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
namespace GroundTheory.Heights₂.Heights.Targets
namespace ProjFullRankDense
theorem _root_.solution (hOpen : ProjRegularClosureOpen.Statement)
    (hMeet : ProjFullRankMeetsRegular.Statement) : ProjFullRankDense.Statement := by
  intro K _ ι _ P J n R Ψ V BV hH hC hΨ x hx
  obtain ⟨y, hyc, hy⟩ := hMeet K ι P J n R Ψ V BV hH hC hΨ x hx
  have hO : IsOpen (closure (projRegular R Ψ BV)) := hOpen K ι P J n R Ψ V BV hH
  have hcl : IsClopen (closure (projRegular R Ψ BV)) := ⟨isClosed_closure, hO⟩
  rw [hO.interior_eq]
  have hsub := hcl.connectedComponent_subset (subset_closure hy)
  rw [← connectedComponent_eq hyc] at hsub
  exact hsub mem_connectedComponent
end ProjFullRankDense
end GroundTheory.Heights₂.Heights.Targets
