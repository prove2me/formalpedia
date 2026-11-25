-- Prove2me | solution 1 for PI.VolStabSW.DeterminantAdmissible.exists_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:20:18.109806+00:00
-- url     : https://prove2.me/submissions/3267184a-f4d9-4e7b-a38a-6298d8c4dd88

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_NuInvSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoPolish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DetAdmA
import Theorems.Thm_PI_VolStabSW_DeterminantAdmissible_isClopen_translate
import Theorems.Thm_PI_VolStabSW_DeterminantAdmissible_isCompact_translate
import Theorems.Thm_PI_VolStabSW_DeterminantAdmissible_mem_translate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.DeterminantAdmissible
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabSW.PositiveNearLattice MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabSW.DeterminantAdmissible
theorem _root_.solution {W : Set (Fv F v)} (hW : IsOpen W) {t : Fv F v} (ht : t ∈ W) :
    ∃ C, IsClopen C ∧ IsCompact C ∧ t ∈ C ∧ C ⊆ W := by
  obtain ⟨V, hV, htV, hVs⟩ :=
    (loc_compact_Haus_tot_disc_of_zero_dim (H := Fv F v)).exists_subset_of_mem_open
      (⟨ht, mem_translate v t⟩ : t ∈ W ∩
        (Homeomorph.subRight t) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))) (hW.inter (isClopen_translate v t).isOpen)
  exact ⟨V, hV, (isCompact_translate v t).of_isClosed_subset hV.isClosed
    (hVs.trans inter_subset_right), htV, hVs.trans inter_subset_left⟩
end PI.VolStabSW.DeterminantAdmissible
