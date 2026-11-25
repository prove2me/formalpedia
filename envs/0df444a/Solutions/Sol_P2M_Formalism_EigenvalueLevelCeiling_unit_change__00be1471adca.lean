-- Prove2me | solution 1 for P2M_Formalism_EigenvalueLevelCeiling_unit_change__00be1471adca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:37:11.444799+00:00
-- url     : https://prove2.me/submissions/edd44de1-9c0c-4282-bced-c6783a049414

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_UnipotentNumeric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.EigenvalueLevelCeiling
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : UnitChange := by
  unfold UnitChange
  intro ρ x y d r k δ ε hρ hδ
  have hρ' : ρ ≠ 0 := hρ.ne'
  have hδ' : δ ≠ 0 := hδ.ne'
  first
    | (field_simp; ring)
    | field_simp
end Formalism.EigenvalueLevelCeiling
