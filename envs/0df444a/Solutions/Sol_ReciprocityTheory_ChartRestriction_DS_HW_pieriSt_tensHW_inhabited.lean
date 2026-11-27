-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.pieriSt_tensHW_inhabited
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:35:43.337378+00:00
-- url     : https://prove2.me/submissions/7878ed0a-27e7-46ea-90fa-1950686937c9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_StTest
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pieriSt_kRel_stdM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pieriSt_stdM_diag

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) :
    Formalism.REAL.KRel ε (0 : Fin n → Fin n → Module.End ℂ ℂ) ∧
    Formalism.REAL.KUnit ε (0 : Fin n → Fin n → Module.End ℂ ℂ) ∧
    Formalism.REAL.KHighest ε (0 : Fin n → Fin n → Module.End ℂ ℂ) 0 (1 : ℂ) ∧
    Formalism.REAL.kSpan ε (0 : Fin n → Fin n → Module.End ℂ ℂ) (1 : ℂ) = ⊤ ∧
    Formalism.REAL.KRel ε (stdM n) ∧
    (∀ a, stdM n a a = Matrix.diagonal fun i => ((stdWt n i a : ℝ) : ℂ)) := by
  refine ⟨?_, ?_, ?_, ?_, pieriSt_kRel_stdM ε, pieriSt_stdM_diag⟩
  · intro a b c d _ _; simp
  · intro a b _ x y; simp
  · exact ⟨fun a => by simp, fun a b _ _ => by simp⟩
  · refine eq_top_iff.mpr fun v _ => ?_
    simp only [Formalism.REAL.kSpan, Submodule.mem_sInf, Set.mem_ofPred_eq]
    rintro S ⟨h1, _⟩
    have : v = v • (1 : ℂ) := by simp
    rw [this]
    exact S.smul_mem v h1
end ReciprocityTheory.ChartRestriction.DS.HW
