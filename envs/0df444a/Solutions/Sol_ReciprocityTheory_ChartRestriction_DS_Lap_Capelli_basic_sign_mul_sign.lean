-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.basic_sign_mul_sign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:38.270618+00:00
-- url     : https://prove2.me/submissions/cd0001fa-96ad-40c7-a8ad-7132a631114b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc

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
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {p : ℕ} (τ σ : Equiv.Perm (Fin p)) :
    ((Equiv.Perm.sign τ : ℤˣ) : ℤ) * ((Equiv.Perm.sign (τ * σ) : ℤˣ) : ℤ) = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) := by
  rw [← Units.val_mul, Equiv.Perm.sign_mul, ← mul_assoc, Int.units_mul_self, one_mul]
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
