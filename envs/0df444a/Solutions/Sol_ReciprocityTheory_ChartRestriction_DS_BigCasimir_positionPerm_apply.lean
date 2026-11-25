-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.BigCasimir.positionPerm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:59.79259+00:00
-- url     : https://prove2.me/submissions/b2b2df41-4f3b-4429-a102-d848e3f0505e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.BigCasimir
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS.BigCasimir
theorem _root_.solution {k : ℕ} (i : Fin k) (τ : Equiv.Perm (Fin n × Fin n)) (κ : Fin k → Fin n × Fin n) :
    positionPerm i τ κ = Function.update κ i (τ (κ i)) := rfl
end ReciprocityTheory.ChartRestriction.DS.BigCasimir
