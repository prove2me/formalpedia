-- Prove2me | solution 1 for QPK.Bru.gf_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:04:19.526748+00:00
-- url     : https://prove2.me/submissions/7ec6fd1a-fb8b-4b64-ae54-dbec04d21d51

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
theorem _root_.solution (μ : Measure G) (K : ℕ → Set G) (S : Set G) (h1 : (1 : G) ∈ S)
    (hpos : PosOn μ S) (n : ℕ) {x : G} (hx : x ∈ interior (K n)) : gf μ K n x ≠ 0 := by
  intro h0
  have hU : IsOpen ((fun s => s * x) ⁻¹' interior (K n)) :=
    isOpen_interior.preimage (continuous_mul_right x)
  have hne := hpos _ hU ⟨1, by simpa using hx, h1⟩
  exact hne (measure_mono_null (Set.preimage_mono interior_subset) h0)
end QPK.Bru
