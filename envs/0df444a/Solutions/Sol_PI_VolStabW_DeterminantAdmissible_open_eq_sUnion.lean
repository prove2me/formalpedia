-- Prove2me | solution 1 for PI.VolStabW.DeterminantAdmissible.open_eq_sUnion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:05:48.278981+00:00
-- url     : https://prove2.me/submissions/00304494-0cf0-4fab-99d7-c51e0d8370fe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuInvSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoAF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoPolish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmA
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_exists_cc

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
  PI.VolStabW.PositiveNearLattice MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabW.DeterminantAdmissible
theorem _root_.solution {W : Set (Fv F v)} (hW : IsOpen W) :
    ∃ T : Set (Set (Fv F v)), T.Countable ∧ (∀ C ∈ T, IsClopen C ∧ IsCompact C) ∧ W = ⋃₀ T := by
  obtain ⟨T, hT, he⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun i : {C : Set (Fv F v) // IsClopen C ∧ IsCompact C ∧ C ⊆ W} => (i.1 : Set (Fv F v)))
    fun i => i.2.1.isOpen
  refine ⟨Subtype.val '' T, hT.image _, ?_, ?_⟩
  · rintro _ ⟨i, -, rfl⟩
    exact ⟨i.2.1, i.2.2.1⟩
  · rw [sUnion_image, he]
    ext t
    constructor
    · intro ht
      obtain ⟨C, h1, h2, h3, h4⟩ := exists_cc v hW ht
      exact mem_iUnion.2 ⟨⟨C, h1, h2, h4⟩, h3⟩
    · intro ht
      obtain ⟨i, hi⟩ := mem_iUnion.1 ht
      exact i.2.2.2 hi
end PI.VolStabW.DeterminantAdmissible
