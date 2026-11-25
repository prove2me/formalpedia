-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.CardG.coord_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:32:50.700705+00:00
-- url     : https://prove2.me/submissions/dce62165-f6f1-4ba4-a9de-b43eba9ecf5f

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
theorem _root_.solution (L : PeriodPair) {m n m' n' : ℤ}
    (h : (m : ℂ) * L.ω₁ + n * L.ω₂ = m' * L.ω₁ + n' * L.ω₂) : m = m' ∧ n = n' := by
  have hi := LinearIndependent.pair_iff.mp L.indep ((m - m' : ℤ) : ℝ) ((n - n' : ℤ) : ℝ) (by
    simp only [Complex.real_smul]; push_cast; linear_combination h)
  constructor
  · have := hi.1
    have h2 : m - m' = 0 := by exact_mod_cast this
    omega
  · have := hi.2
    have h2 : n - n' = 0 := by exact_mod_cast this
    omega
end ReciprocityTheory.ChartRestriction.L1.CardG
