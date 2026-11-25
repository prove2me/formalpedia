-- Prove2me | solution 1 for QPK.Bru.Eset_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:04:16.738937+00:00
-- url     : https://prove2.me/submissions/c475cf8a-ff8e-4863-878c-f98258be81a8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_BruhatDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open QPK
open QPK.Bru
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace QPK.Bru
theorem _root_.solution (μ : Measure G) (K : ℕ → Set G) (x : G) (h : ∃ n, gf μ K n x ≠ 0) :
    ∃ n, x ∈ Eset μ K n := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, fun k hk => ?_⟩
  by_contra hc
  exact Nat.find_min h hk hc
end QPK.Bru
