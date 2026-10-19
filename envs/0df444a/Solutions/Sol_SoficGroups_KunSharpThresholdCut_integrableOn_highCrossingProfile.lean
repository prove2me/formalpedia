-- Prove2me | solution 1 for SoficGroups.KunSharpThresholdCut.integrableOn_highCrossingProfile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/7a89a66f-3c35-4984-a723-b03e47d2a5c4

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunSharpThresholdCut_integrableOn_crossingIndicator

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunSharpThresholdCut
open MeasureTheory Set
open scoped BigOperators ENNReal symmDiff
namespace SoficGroups.KunSharpThresholdCut
theorem _root_.solution {V ι : Type*}
    [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (a c d : ℝ) :
    IntegrableOn (highCrossingProfile σ f a) (Ioo c d) := by
  unfold highCrossingProfile
  exact integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun x _ =>
      integrableOn_crossingIndicator (f (σ i x)) (f x) c d
end SoficGroups.KunSharpThresholdCut
