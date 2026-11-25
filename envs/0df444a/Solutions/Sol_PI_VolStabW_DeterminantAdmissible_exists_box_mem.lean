-- Prove2me | solution 1 for PI.VolStabW.DeterminantAdmissible.exists_box_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:55:55.845693+00:00
-- url     : https://prove2.me/submissions/8c59694c-41a4-426b-b23e-6651444e5e64

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmB
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_isClopen_translate
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_isCompact_translate
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_mem_translate


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.DeterminantAdmissible
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
namespace PI.VolStabW.DeterminantAdmissible
theorem _root_.solution (y : ι → Af F) : ∃ D, IsBoxD D ∧ y ∈ boxS D := by
  classical
  let D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) := fun c v =>
    if y c v ∈ v.adicCompletionIntegers F then (v.adicCompletionIntegers F : Set (Fv F v))
    else (Homeomorph.subRight (y c v)) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))
  refine ⟨D, ⟨fun c v => ?_, ?_⟩, fun c v => ?_⟩
  · by_cases h : y c v ∈ v.adicCompletionIntegers F
    · rw [show D c v = _ from if_pos h]
      exact ⟨isClopen_intV v, isCompact_intV v⟩
    · rw [show D c v = _ from if_neg h]
      exact ⟨isClopen_translate v _, isCompact_translate v _⟩
  · filter_upwards [eventually_all.2 fun c => (y c).eventually] with v hv c
    exact if_pos (hv c)
  · by_cases h : y c v ∈ v.adicCompletionIntegers F
    · rw [show D c v = _ from if_pos h]
      exact h
    · rw [show D c v = _ from if_neg h]
      exact mem_translate v _
end PI.VolStabW.DeterminantAdmissible
