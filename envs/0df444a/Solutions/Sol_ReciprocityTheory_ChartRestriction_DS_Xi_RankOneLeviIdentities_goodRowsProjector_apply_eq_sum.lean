-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.goodRowsProjector_apply_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:47:30.928153+00:00
-- url     : https://prove2.me/submissions/ca997ce9-8f45-4225-8da3-126bd581c24f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight

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
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
theorem _root_.solution (p : Fin (2 * (1 + r') + k + 1)) : e0 k r' p = if p.val = 0 then 1 else 0 := by
  unfold e0 bvec
  rw [Pi.single_apply]
  congr 1
  apply propext
  rw [Fin.ext_iff]
  simp [eI, a0]
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
