-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__isSFiniteKernel_of_forall_univ_lt_top_f4df5b9f1781
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:38:03.912858+00:00
-- url     : https://prove2.me/submissions/3d46bee5-5a20-4e8b-868a-96cb75ee7bd7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductFubini

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology ProbabilityTheory
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂
theorem _root_.solution {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (η : Kernel α β) (h : ∀ a, η a Set.univ < ⊤) : IsSFiniteKernel η := by
  classical
  have hmeas : Measurable fun a => η a Set.univ := η.measurable_coe MeasurableSet.univ
  let g : α → ℕ := fun a => ⌊(η a Set.univ).toReal⌋₊
  have hg : Measurable g := Nat.measurable_floor.comp hmeas.ennreal_toReal
  have hB : ∀ j : ℕ, MeasurableSet (g ⁻¹' {j}) := fun j => hg (measurableSet_singleton j)
  let ηs : ℕ → Kernel α β := fun j => Kernel.piecewise (hB j) η 0
  have hfin : ∀ j, IsFiniteKernel (ηs j) := by
    intro j
    refine ⟨⟨(j : ℝ≥0∞) + 1, by simp [ENNReal.add_lt_top], fun a => ?_⟩⟩
    by_cases ha : a ∈ g ⁻¹' {j}
    · have hj : g a = j := ha
      have h1 : (η a Set.univ).toReal < (j : ℝ) + 1 := by
        have := Nat.lt_floor_add_one (η a Set.univ).toReal
        simpa [g, hj] using this
      have h2 : η a Set.univ = ENNReal.ofReal (η a Set.univ).toReal :=
        (ENNReal.ofReal_toReal (h a).ne).symm
      simp only [ηs, Kernel.piecewise_apply, if_pos ha]
      rw [h2]
      refine ENNReal.ofReal_le_of_le_toReal ?_
      rw [ENNReal.toReal_add (by simp) (by simp)]
      simpa using h1.le
    · have ha' : ¬ g a = j := ha
      simp [ηs, Kernel.piecewise_apply, ha']
  have hsum : η = Kernel.sum ηs := by
    ext a s hs
    rw [Kernel.sum_apply, Measure.sum_apply _ hs, tsum_eq_single (g a)]
    · simp [ηs, Kernel.piecewise_apply]
    · intro j hj
      have ha' : ¬ g a = j := fun h' => hj h'.symm
      simp [ηs, Kernel.piecewise_apply, ha']
  rw [hsum]
  exact ⟨⟨fun j => ηs j, hfin, rfl⟩⟩
end GlobalTheory.CompanionTheory.SW.PiLocalization₂
