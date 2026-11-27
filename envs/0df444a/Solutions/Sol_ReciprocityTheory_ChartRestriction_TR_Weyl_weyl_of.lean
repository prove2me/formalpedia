-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.weyl_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:29:09.189488+00:00
-- url     : https://prove2.me/submissions/d024ceb3-5a84-4ddd-a22a-ecbddd6a296b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_Branch
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_BlockCombStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_Statement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_ne_zero_of_toMK_diag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_antitone_blk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_weylGT


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl
open ReciprocityTheory.ChartRestriction.DS.S7
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
theorem _root_.solution (hK : KCharGTStatement) (hB : BlockCombStatement) : WeylStatement := by
  have hW : WeylGTStatement := weylGT
  intro n ε Λ hdom T k t hk
  rw [hK n ε Λ hdom T k t hk]
  obtain ⟨hw, hnum, hrho⟩ := hB ℂ n ε (Λ + rhoK ε) t
  rw [hw, hnum]
  have hG : ∀ b : Bool, wden (cnt ε b) (t ∘ blk ε b) * gtChar (cnt ε b) (Λ ∘ blk ε b) (t ∘ blk ε b) =
      alt (cnt ε b) ((Λ + rhoK ε) ∘ blk ε b) (t ∘ blk ε b) := by
    intro b
    have hc : (Λ + rhoK ε) ∘ blk ε b = Λ ∘ blk ε b + delta (cnt ε b) := by
      rw [← hrho b]
      rfl
    rw [hc]
    exact hW ℂ _ _ (antitone_blk hdom b) _ (fun i => ne_zero_of_toMK_diag k hk _)
  rw [← hG true, ← hG false]
  ring
end ReciprocityTheory.ChartRestriction.TR.Weyl
