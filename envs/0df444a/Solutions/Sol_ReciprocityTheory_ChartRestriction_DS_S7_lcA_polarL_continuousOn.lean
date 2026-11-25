-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.lcA_polarL_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:30:22.800181+00:00
-- url     : https://prove2.me/submissions/498b0eeb-87c8-4584-839a-b4c21244ec54

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LocalA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_isSelfAdjoint_isUnit_spectrum_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
open scoped Matrix.Norms.L2Operator
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ε : Fin n → Bool) :
    ContinuousOn (PolarDecomposition.polar_L (n := n)) {g | inUJ ε g} := by
  have h : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => CFC.log (gᴴ * g)) {g | inUJ ε g} := by
    refine CFC.continuousOn_log.comp (by fun_prop) ?_
    intro g hg
    obtain ⟨hsa, hu, -⟩ := PolarDecomposition.polar_isSelfAdjoint_isUnit_spectrum_pos hg
    exact ⟨hsa, hu⟩
  exact h.const_smul (1 / 2 : ℝ)
end ReciprocityTheory.ChartRestriction.DS.S7
