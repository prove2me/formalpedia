-- Prove2me | solution 1 for PI.NglqJacSplitW.chiM_diagOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:03:52.328169+00:00
-- url     : https://prove2.me/submissions/b2186abf-8f40-44a2-9c70-dfd3f900029c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_FactorOneOfDiscrete
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_GoodTransvection
import Theorems.Thm_PI_NglqJacSplitW_chiM_spec
import Theorems.Thm_PI_NglqJacSplitW_exists_test_set

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal
open PI PI.NglqJacSplitW
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.NglqJacSplitW
theorem _root_.solution (hD : DiagOne) (i : ι) (a : F) (ha : a ≠ 0)
    (h : IsUnit (diagonal (Function.update (1 : ι → F) i a)).det) :
    (chiM (diagonal (Function.update (1 : ι → F) i a)) h : ℝ≥0∞) = modF F a := by
  let _ : MeasurableSpace (ι → F) := borel _
  have _ : BorelSpace (ι → F) := ⟨rfl⟩
  obtain ⟨K, hKm, hK0, hKt⟩ := exists_test_set (Measure.addHaar : Measure (ι → F))
  have h1 := chiM_spec _ h (Measure.addHaar : Measure (ι → F)) K
  have h2 := hD F ι i a ha (Measure.addHaar : Measure (ι → F)) inferInstance K hKm
  have hfun : (fun x => diagonal (Function.update (1 : ι → F) i a) *ᵥ x) = fun x => Function.update x i (a * x i) := by
    funext x j
    by_cases hj : j = i
    · subst hj
      simp [Matrix.mulVec_diagonal]
    · simp [Matrix.mulVec_diagonal, Function.update_of_ne hj]
  rw [hfun] at h1
  rw [h1] at h2
  exact (ENNReal.mul_left_inj hK0 hKt).mp h2
end PI.NglqJacSplitW
