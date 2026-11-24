-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.inner_bvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:01:24.216847+00:00
-- url     : https://prove2.me/submissions/da7c43d5-0807-4028-bd94-d5bdf7dfca18

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExistsKmat

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
theorem _root_.solution (i : Fin (2 * r + k + 1)) (v : Fin (2 * r + k + 1) → ℂ) :
    inner ℂ (WithLp.toLp 2 (bvec i) : EE k r) (WithLp.toLp 2 v) = v i := by
  first
    | (simp [bvec, PiLp.inner_apply, Pi.single_apply])
    | (show inner ℂ (EuclideanSpace.single i (1 : ℂ)) (WithLp.toLp 2 v : EE k r) = v i
       rw [EuclideanSpace.inner_single_left]; simp)
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
