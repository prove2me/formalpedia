-- Prove2me | solution 1 for QPK.Bru.gf_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:03:11.017116+00:00
-- url     : https://prove2.me/submissions/706e9a75-9f74-412b-9c27-bdc3b49b3d8e

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
theorem _root_.solution (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (K : ℕ → Set G)
    (hK : ∀ n, IsCompact (K n)) (n : ℕ) (x : G) : gf μ K n x < ⊤ := by
  have h : IsCompact ((fun s => s * x) ⁻¹' K n) :=
    (Homeomorph.mulRight x).isCompact_preimage.2 (hK n)
  exact h.measure_lt_top
end QPK.Bru
