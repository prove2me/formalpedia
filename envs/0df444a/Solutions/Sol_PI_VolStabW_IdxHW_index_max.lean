-- Prove2me | solution 1 for PI.VolStabW.IdxHW.index_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:56:55.018851+00:00
-- url     : https://prove2.me/submissions/e9ee17d4-c229-4319-8d13-eb6c901339c4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxE
import Theorems.Thm_ReciprocityTheory_Bridge_ResidueFieldCardinality_card_residue


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing
open PI.VolStabW.IdxHW
namespace PI.VolStabW.IdxHW
theorem _root_.solution {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup.index = Nat.card (𝓞 F ⧸ v.asIdeal) := by
  rw [← ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue v]
  rfl
end PI.VolStabW.IdxHW
