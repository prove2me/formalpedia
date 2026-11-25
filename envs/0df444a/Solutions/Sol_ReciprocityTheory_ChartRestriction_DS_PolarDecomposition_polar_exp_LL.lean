-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_exp_LL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:18.393836+00:00
-- url     : https://prove2.me/submissions/881557dd-9d51-4a2f-9458-b22b949ce629

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_exp_log
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_L_add
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
open Finset Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
namespace ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
theorem _root_.solution {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    NormedSpace.exp (polar_L g + polar_L g) = gᴴ * g := by
  have hf := polar_isSelfAdjoint_isUnit_spectrum_pos hg
  rw [polar_L_add]
  exact polar_exp_log hf.1 hf.2.2
end ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
