-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.CardG.co_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:01:30.115425+00:00
-- url     : https://prove2.me/submissions/871788f1-ebee-44cb-9b67-f3a365b31fb3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedHalf
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedCardG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open ReciprocityTheory.ChartRestriction.L1.CardG
namespace ReciprocityTheory.ChartRestriction.L1.CardG
theorem _root_.solution (L : PeriodPair) {z : ℂ} (h : z ∈ L.lattice) :
    ((co L z).1 : ℂ) * L.ω₁ + ((co L z).2 : ℂ) * L.ω₂ = z := by
  rw [co, dif_pos h]
  exact (PeriodPair.mem_lattice.mp h).choose_spec.choose_spec
end ReciprocityTheory.ChartRestriction.L1.CardG
