-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.exists_e_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:43:33.189977+00:00
-- url     : https://prove2.me/submissions/1e8ad880-1f9f-4577-b2a4-467cae68ce91

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_exists_of_ratRoot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Om_isAlgebraic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane Pointwise
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {d l : ℕ} [Fact l.Prime] (e : Om d →+* PadicAlgCl l)
    (r : PadicAlgCl l →+* PadicAlgCl l) (x : Om d) : ∃ y : Om d, e y = r (e x) := by
  obtain ⟨p, hp, hpx⟩ := Om_isAlgebraic d x
  have : IsAlgClosed (Om d) := (inferInstance : IsAlgClosure (KQ d) (Om d)).isAlgClosed
  let f₀ : ℚ →+* Om d := algebraMap ℚ (Om d)
  have h0 : p.eval₂ f₀ x = 0 := by
    apply (algebraMap (Om d) ℂ).injective
    rw [Polynomial.hom_eval₂, map_zero]
    have : (algebraMap (Om d) ℂ).comp f₀ = algebraMap ℚ ℂ := Subsingleton.elim _ _
    rw [this]
    exact hpx
  refine exists_of_ratRoot e f₀ ((r.comp e).comp f₀) hp ?_
  have := congrArg (r.comp e) h0
  rw [Polynomial.hom_eval₂, map_zero] at this
  exact this
end ReciprocityTheory.ChartRestriction.L1
