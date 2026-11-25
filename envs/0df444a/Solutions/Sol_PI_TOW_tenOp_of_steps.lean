-- Prove2me | solution 1 for PI.TOW.tenOp_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:29:38.390463+00:00
-- url     : https://prove2.me/submissions/5e26395a-f5bc-4e22-92fd-0bc5f06b53ee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FockRBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW
open PI.TO
namespace PI.TOW
theorem _root_.solution (hD : StepDeg) (hP : StepPure) (hS : StepSpan) : PI.TenOp := by
  intro hFP hSB K _ _ n' m hm vec TT d c ν hν hc h0 β hβ s hs
  obtain ⟨f, hf, heq⟩ := hS K n' m vec TT d c (fun t => PI.TO.dualWeyl K (m + 1) (m + 1) (ν t))
    (fun B S hB hS' => hP hFP hSB K n' m hm vec TT d c ν hν hc h0 B S hB hS') β hβ s hs
  have hsum : ∀ G, (∑ l ∈ f.support, f l • PI.TO.opWord l G) = combo f G :=
    fun G => rfl
  refine ⟨f.support, f, hf, fun G hG => ⟨?_, fun H hH => ?_⟩⟩
  · exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hD K n' (m + 1) d l G hG)
  · rw [hsum]
    exact heq G hG H hH
end PI.TOW
