-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.whB_g_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:38.858628+00:00
-- url     : https://prove2.me/submissions/2889f33b-fd8b-4f33-9f37-091b346395f8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliWhittakerZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {M R : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℂ R]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {k r : ℕ} (ψ : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ) {a : Fin (k + 2 * r + 1)}
    (h : ∀ b, ¬ IsSimplePair k r a b) : whB_g k r ψ a = 1 :=
  Finset.prod_eq_one fun b _ => if_neg (h b)
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
