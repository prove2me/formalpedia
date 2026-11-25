-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.bAll_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:20:47.657177+00:00
-- url     : https://prove2.me/submissions/d0dd2ef5-eaa3-4524-b0de-8e6dab30afce

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiExists2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi
theorem _root_.solution (hb : BStepBase) (hs : BStepSucc) :
    ∀ k r : ℕ, 1 ≤ k → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → BAt k r δ := by
  intro k r hk
  induction r with
  | zero => intro δ hδ _; exact hb k hk δ hδ
  | succ r' ih =>
    intro δ hδ hδ'
    exact hs k (r' + 1) r' (by omega) hk δ hδ hδ' (ih (δ / 4) (by positivity) (by linarith))
end ReciprocityTheory.ChartRestriction.DS.Xi
