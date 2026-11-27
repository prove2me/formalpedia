-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.pieriSt_mem_khwSub_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:30:32.130846+00:00
-- url     : https://prove2.me/submissions/b0e4d36a-1ef3-4940-8cb0-ad57b84ba32a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_StTest

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
theorem _root_.solution {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ W) (ν : Fin n → ℝ) (v : W) :
    v ∈ khwSub ε E ν ↔ Formalism.REAL.KHighest ε E ν v := by
  simp only [khwSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero, Formalism.REAL.KHighest,
    Formalism.REAL.IsWeight]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a => by simpa using h1 a, fun a b hab he => h2 a b ⟨hab, he⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun a => by simpa using h1 a, fun a b h => h2 a b h.1 h.2⟩
end ReciprocityTheory.ChartRestriction.DS.HW
