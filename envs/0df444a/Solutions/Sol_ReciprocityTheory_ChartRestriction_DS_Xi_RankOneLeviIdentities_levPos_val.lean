-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.levPos_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:44:58.091725+00:00
-- url     : https://prove2.me/submissions/e197c562-9c74-466f-a9fd-77afe97b936a

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
theorem _root_.solution (j : Fin (2 * r' + k + 1)) : (levPos k 1 r' j).val = j.val + 1 := rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
