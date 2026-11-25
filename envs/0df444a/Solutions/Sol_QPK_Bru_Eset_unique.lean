-- Prove2me | solution 1 for QPK.Bru.Eset_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:03:04.478386+00:00
-- url     : https://prove2.me/submissions/0def1ad8-481e-48c6-b068-e41e05cca297

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
theorem _root_.solution {μ : Measure G} {K : ℕ → Set G} {x : G} {n m : ℕ}
    (hn : x ∈ Eset μ K n) (hm : x ∈ Eset μ K m) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · exact absurd (hm.2 n h) hn.1
  · exact h
  · exact absurd (hn.2 m h) hm.1
end QPK.Bru
