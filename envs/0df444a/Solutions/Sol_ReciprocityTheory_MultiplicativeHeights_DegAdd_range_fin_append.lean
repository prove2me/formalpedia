-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DegAdd.range_fin_append
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:16:31.645807+00:00
-- url     : https://prove2.me/submissions/fa328fec-8a8c-4b65-a5e7-301ee36f52a0

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_Lemmata_GeneralBFactBisAlt_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.MultiplicativeHeights.DegAdd
open NumberField
namespace ReciprocityTheory.MultiplicativeHeights.DegAdd
theorem _root_.solution {α : Type} {k m : ℕ} (b : Fin k → α) (c : Fin m → α) :
    Set.range (Fin.append b c) = Set.range b ∪ Set.range c := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left i => exact Or.inl ⟨i, (Fin.append_left b c i).symm⟩
    | right j => exact Or.inr ⟨j, (Fin.append_right b c j).symm⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd m i, Fin.append_left b c i⟩
    · exact ⟨Fin.natAdd k j, Fin.append_right b c j⟩
end ReciprocityTheory.MultiplicativeHeights.DegAdd
