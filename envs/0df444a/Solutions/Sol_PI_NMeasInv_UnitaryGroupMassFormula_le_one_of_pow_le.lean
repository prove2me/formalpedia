-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.le_one_of_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:57:40.846399+00:00
-- url     : https://prove2.me/submissions/212e7436-e4e3-4731-adda-049d6f0a9f10

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_RightInvOfContract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology
open scoped ENNReal NNReal
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
attribute [local instance] Classical.propDecidable
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution {x B : ℝ≥0∞} (hB : B ≠ ⊤) (h : ∀ p : ℕ, x ^ p ≤ B) : x ≤ 1 := by
  by_contra hx
  push_neg at hx
  have hxt : x ≠ ⊤ := by
    rintro rfl
    have h1 := h 1
    simp at h1
    exact hB h1
  obtain ⟨p, hp⟩ := pow_unbounded_of_one_lt B.toReal (by
    have h2 := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hxt).mpr hx
    simpa using h2)
  have h3 : (x ^ p).toReal ≤ B.toReal := ENNReal.toReal_mono hB (h p)
  rw [ENNReal.toReal_pow] at h3
  linarith
end PI.NMeasInv.UnitaryGroupMassFormula
