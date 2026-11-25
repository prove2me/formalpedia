-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.sq_rho_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:13:14.228285+00:00
-- url     : https://prove2.me/submissions/f33f8125-c8d7-4ad7-ab14-ab17316159ae

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqCharA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_ext_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_ext_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_ext_intl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
theorem _root_.solution {k : ℕ} (μ : Fin (k + 1) → ℤ) (hμ : 0 ≤ μ (Fin.last k)) :
    Function.Surjective (sq_rho μ) := by
  intro g
  refine ⟨⟨sq_ext μ g.1, sq_ext_intl μ hμ g, sq_ext_sum μ hμ g⟩, ?_⟩
  apply Subtype.ext
  funext a t
  exact sq_ext_cc μ g.1 a t
end ReciprocityTheory.ChartRestriction.TR.Weyl
