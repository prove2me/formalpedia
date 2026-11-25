-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.tensHW_hw_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:16.008651+00:00
-- url     : https://prove2.me/submissions/2c15f943-079a-4943-ba92-faa7f5af29b4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_LowComp
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensHW
import Theorems.Thm_Formalism_REAL_kHiUniq


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
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {A : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {w : V}
    (hA : Formalism.REAL.KRel ε A) (hU : Formalism.REAL.KUnit ε A) (hw : Formalism.REAL.KHighest ε A Λ w)
    (hspan : Formalism.REAL.kSpan ε A w = ⊤) {μ : Fin n → ℝ} {y : V}
    (hy : Formalism.REAL.KHighest ε A μ y) (hy0 : y ≠ 0) :
    μ = Λ ∧ ∃ c : ℂ, y = c • w := by
  rcases Formalism.REAL.kHiUniq V n ε A Λ μ w y hA hU hw (by rw [hspan]; exact Submodule.mem_top) hy with h | h
  · exact absurd h hy0
  · exact h
end ReciprocityTheory.ChartRestriction.DS.HW
