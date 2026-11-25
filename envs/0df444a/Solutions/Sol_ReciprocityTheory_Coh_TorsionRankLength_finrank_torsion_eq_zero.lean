-- Prove2me | solution 1 for ReciprocityTheory.Coh.TorsionRankLength.finrank_torsion_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:48:34.264701+00:00
-- url     : https://prove2.me/submissions/57088755-370a-4daf-93aa-3b300a33852f

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_RankLenA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.TorsionRankLength
universe u
open Module Submodule Function
open scoped Pointwise TensorProduct
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (H : Type u) [AddCommGroup H] [Module R H] [Module.Finite R H]
namespace ReciprocityTheory.Coh.TorsionRankLength
theorem _root_.solution : Module.finrank R (torsion R H) = 0 := by
  rw [Module.finrank_eq_zero_iff]
  intro x
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (x : H)).1 x.2
  exact ⟨a, nonZeroDivisors.ne_zero a.2, Subtype.ext ha⟩
end ReciprocityTheory.Coh.TorsionRankLength
