-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFock.integral_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:20:46.15839+00:00
-- url     : https://prove2.me/submissions/9da0c5a3-4b31-4452-8a25-d288fcf45959

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_FockSpaces_VolumeIsAddHaar
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFock_measure_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFock
variable {G H K : Type}
  [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H] [LocallyCompactSpace H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace K] [AddCommGroup K] [IsTopologicalAddGroup K] [LocallyCompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K]
namespace PositivityTheory.SiegelWeilFormula.KFock
theorem _root_.solution (ν : Measure G) [ν.IsAddHaarMeasure] (la : Measure H) [la.IsAddHaarMeasure]
    (mu : Measure K) [mu.IsAddHaarMeasure] (Φ : H × K ≃ₜ+ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : G → ℂ, ∫ x, g x ∂ν = C * ∫ p, g (Φ p) ∂(la.prod mu) := by
  obtain ⟨c, hc, hν⟩ := measure_split ν la mu Φ
  refine ⟨c, by exact_mod_cast hc, fun g => ?_⟩
  have hm := integral_map_equiv (μ := la.prod mu) (Φ.toHomeomorph.toMeasurableEquiv) g
  rw [hν, integral_smul_nnreal_measure]
  erw [hm]
  simp [NNReal.smul_def, Complex.real_smul]
  exact Or.inl rfl
end PositivityTheory.SiegelWeilFormula.KFock
