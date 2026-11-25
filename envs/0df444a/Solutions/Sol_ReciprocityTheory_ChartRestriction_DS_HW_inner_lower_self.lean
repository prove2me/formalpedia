-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.inner_lower_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:32.518315+00:00
-- url     : https://prove2.me/submissions/a954b6a0-e377-415f-8942-ae994fbabd03

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Weight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KtintExpApplyOfEig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_InnerLowerSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {A : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {w : V}
    (hR : Formalism.REAL.KRel ε A) (hU : Formalism.REAL.KUnit ε A) (hw : Formalism.REAL.KHighest ε A Λ w)
    {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    ⟪A b a w, A b a w⟫_ℂ = (((Λ a - Λ b : ℝ)) : ℂ) * ⟪w, w⟫_ℂ := by
  have hba : b ≠ a := ne_of_gt hab
  have hc := hR a b b a he he.symm
  simp only [if_true] at hc
  have hx := congrArg (fun F : Module.End ℂ V => F w) hc
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hw.2 a b hab he, map_zero, sub_zero] at hx
  have h1 := hU b a he.symm w (A b a w)
  rw [h1, hx, hw.1 a, hw.1 b, ← sub_smul, inner_smul_right]
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.DS.HW
