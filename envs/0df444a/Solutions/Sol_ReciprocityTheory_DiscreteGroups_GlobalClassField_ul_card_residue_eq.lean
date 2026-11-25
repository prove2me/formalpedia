-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.ul_card_residue_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:48:03.062156+00:00
-- url     : https://prove2.me/submissions/bbf1b4e2-71bf-479a-a5e2-b859f2324ed7

import Mathlib
import Definitions.Def_ReciprocityTheory_ResidueCardinality_ArtinOntoB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_LocPowB
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
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.GlobalClassField
open NumberField IsDedekindDomain
namespace ReciprocityTheory.DiscreteGroups.GlobalClassField
theorem _root_.solution (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) =
      Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue v
end ReciprocityTheory.DiscreteGroups.GlobalClassField
