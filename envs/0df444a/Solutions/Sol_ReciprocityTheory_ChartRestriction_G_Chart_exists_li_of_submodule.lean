-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.exists_li_of_submodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:46:37.545796+00:00
-- url     : https://prove2.me/submissions/e23818f5-14b0-45ed-89ff-8a8c183a564f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open Module
variable {V k : Type} [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field k] [Algebra V k] [FaithfulSMul V k]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {ι' : Type} [Fintype ι'] [DecidableEq ι'] (N : Submodule V (ι' → V)) :
    ∃ v : Fin (finrank V N) → ι' → V, LinearIndependent V v ∧ ∀ i, v i ∈ N := by
  let b := Module.finBasis V N
  exact ⟨fun i => b i, b.linearIndependent.map' N.subtype (Submodule.ker_subtype N), fun i => (b i).2⟩
end ReciprocityTheory.ChartRestriction.G.Chart
