-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.holoOn_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:06:23.045384+00:00
-- url     : https://prove2.me/submissions/c7f59842-ce2b-4caa-8f67-85edd8a5405d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas e X) {W₁ W₂ : Set X} {G₁ G₂ : X → ℂ}
    (h₁ : A.HoloOn W₁ G₁) (h₂ : A.HoloOn W₂ G₂) :
    A.HoloOn (W₁ ∩ W₂) (fun z => G₁ z + G₂ z) := fun j w hw =>
  ((h₁ j w ⟨hw.1, hw.2.1⟩).add (h₂ j w ⟨hw.1, hw.2.2⟩))
end ReciprocityTheory.AnForm.M
