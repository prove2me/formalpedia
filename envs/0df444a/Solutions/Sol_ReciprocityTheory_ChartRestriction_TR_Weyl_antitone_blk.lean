-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.antitone_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:12.37407+00:00
-- url     : https://prove2.me/submissions/e4a5ba33-8d8a-4342-a97c-f31d203f4995

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_Branch
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_BlockCombStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_Statement
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl
open ReciprocityTheory.ChartRestriction.DS.S7
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℤ}
    (hdom : ∀ a b, a < b → ε a = ε b → Λ b ≤ Λ a) (b : Bool) : Antitone (Λ ∘ blk ε b) := by
  have hmem : ∀ r, ε (blk ε b r) = b := by
    intro r
    have hr := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = b) rfl r
    show ε ((univ.filter fun i : Fin n => ε i = b).orderEmbOfFin rfl r) = b
    simpa using hr
  have hsm : StrictMono (blk ε b) :=
    (Finset.orderEmbOfFin (univ.filter fun i : Fin n => ε i = b) rfl).strictMono
  intro i j hij
  rcases hij.lt_or_eq with h | h
  · exact hdom _ _ (hsm h) ((hmem i).trans (hmem j).symm)
  · rw [h]
end ReciprocityTheory.ChartRestriction.TR.Weyl
