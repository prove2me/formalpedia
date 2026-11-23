-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.isGlRep_iff_glRelR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:33.563321+00:00
-- url     : https://prove2.me/submissions/d605067a-fa23-4142-a71c-94e2b38e50c3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement

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
universe u v w
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ M) : IsGlRep E ↔ GlRelR E :=
  Iff.rfl
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
