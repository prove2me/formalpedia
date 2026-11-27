-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_denIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:27:42.672536+00:00
-- url     : https://prove2.me/submissions/2e7c7b21-e20c-4807-b43e-c5f910b88c36

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Localization.Integer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_MemRangeOfForallHeightOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.KrullAlg
variable {A : Type*} [CommRing A] [IsDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K]
omit [IsDomain A] [IsFractionRing A K]
namespace ReciprocityTheory.ChartRestriction.G.Out.KrullAlg
theorem _root_.solution {ι : Type*} {x : ι → K} {r : A} :
    r ∈ denIdeal (A := A) x ↔ ∀ i, algebraMap A K r * x i ∈ (algebraMap A K).range := Iff.rfl
end ReciprocityTheory.ChartRestriction.G.Out.KrullAlg
