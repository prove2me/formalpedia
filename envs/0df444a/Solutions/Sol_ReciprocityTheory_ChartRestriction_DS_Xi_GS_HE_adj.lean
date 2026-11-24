-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.HE_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:40:56.431572+00:00
-- url     : https://prove2.me/submissions/1746461c-9dbc-4a70-9cbe-bac929d5cf9e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_sgn_sig
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_star_sgn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_hpk_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_HE_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GS
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS
theorem _root_.solution (x y : EE k r) : inner ℂ (HE k r x) y = inner ℂ x (HE k r y) := by
  simp only [HE_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, hpk_mulVec, Pi.star_apply]
  refine Fintype.sum_equiv (sigE k r) _ _ (fun i => ?_)
  simp only [sigE, Equiv.coe_fn_mk, sig_sig, sgn_sig, star_mul', star_sgn]; ring
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
