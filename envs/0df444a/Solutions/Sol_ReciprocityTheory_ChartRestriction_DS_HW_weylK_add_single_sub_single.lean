-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.weylK_add_single_sub_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:46:56.365307+00:00
-- url     : https://prove2.me/submissions/ed4b5220-89f1-47c1-b345-d2a6a3ab5972

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylRatio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylK_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ)
    (i j : Fin n) (hij : ε i ≠ ε j) :
    weylK ε (Λ + ((Pi.single i (1 : ℝ) : Fin n → ℝ) - Pi.single j 1)) = weylK ε Λ *
      (∏ b ∈ univ.filter (fun b => b ≠ i ∧ ε b = ε i),
        ((Λ + rhoC ε) i - (Λ + rhoC ε) b + 1) / ((Λ + rhoC ε) i - (Λ + rhoC ε) b)) *
      (∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j),
        ((Λ + rhoC ε) j - (Λ + rhoC ε) b - 1) / ((Λ + rhoC ε) j - (Λ + rhoC ε) b)) :=
  weylK_two ε Λ hΛ hij
end ReciprocityTheory.ChartRestriction.DS.HW
