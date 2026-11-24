-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.DetB.cst_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:55:22.044678+00:00
-- url     : https://prove2.me/submissions/b81c7920-2900-497a-b2f3-c72f4f246554

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianLiftIdentities

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
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.DetB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.DetB
theorem _root_.solution {k r : ℕ} (H : Mat k r) (v w : Fin (2 * r + k + 1) → ℂ) : 0 ≤ cst H v w :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
end ReciprocityTheory.ChartRestriction.DS.Xi.DetB
