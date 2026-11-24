-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.reflection_apply_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:59:54.653469+00:00
-- url     : https://prove2.me/submissions/f53c65d7-a814-479b-a42e-4f0b78f14191

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
theorem _root_.solution (c : ℂ) (p q : Fin (2 * (1 + r') + k + 1)) :
    w0 k r' c p q = if p.val = 0 ∧ q.val = 2 * (1 + r') + k then (star c)⁻¹
      else if p.val = 2 * (1 + r') + k ∧ q.val = 0 then c
      else if p = q ∧ 0 < p.val ∧ p.val < 2 * (1 + r') + k then 1 else 0 := rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
