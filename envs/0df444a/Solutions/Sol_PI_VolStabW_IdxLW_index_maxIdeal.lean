-- Prove2me | solution 1 for PI.VolStabW.IdxLW.index_maxIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:06:22.51788+00:00
-- url     : https://prove2.me/submissions/3672e4ca-190a-4e7f-9d1e-b0aa83685f0e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHI
import Definitions.Def_ReciprocityTheory_Automorphisms_InstMainA
import Definitions.Def_ReciprocityTheory_ResidueCardinality_ArtinOntoB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHIL
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
open PI.VolStabW.IdxLW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsLocalRing
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabW.IdxLW
theorem _root_.solution :
    (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup.index = Nat.card (𝓞 F ⧸ v.asIdeal) := by
  rw [← ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue v]
  rfl
end PI.VolStabW.IdxLW
