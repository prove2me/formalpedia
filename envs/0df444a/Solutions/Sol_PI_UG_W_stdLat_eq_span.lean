-- Prove2me | solution 1 for PI.UG.W.stdLat_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:15:37.694494+00:00
-- url     : https://prove2.me/submissions/9ab40eff-4131-4a87-bd19-63b24b850099

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_StdLatEqSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UG PI.UG.W
namespace PI.UG.W
theorem _root_.solution (E : Type) [Field E] [NumberField E] (n : ℕ) :
    stdLat E n = Submodule.span (𝓞 E) (Set.range (eStd E n)) := by
  apply le_antisymm
  · intro x hx
    have h' : ∀ i, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = x i := fun i =>
      Submodule.mem_one.mp ((Submodule.mem_pi.mp hx) i (Set.mem_univ i))
    choose a ha using h'
    have hx' : x = ∑ i, a i • eStd E n i := by
      ext k
      simp [eStd, Pi.single_apply, Finset.sum_apply, ← ha, Algebra.smul_def]
    rw [hx']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Submodule.mem_pi.mpr fun k _ => Submodule.mem_one.mpr ?_
    by_cases h : k = i
    · subst h
      exact ⟨1, by simp [eStd]⟩
    · exact ⟨0, by simp [eStd, h]⟩
end PI.UG.W
