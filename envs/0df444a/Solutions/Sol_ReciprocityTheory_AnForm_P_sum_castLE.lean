-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.sum_castLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:46.478985+00:00
-- url     : https://prove2.me/submissions/8d11033c-f9b8-40db-becb-495ce03e2a23

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open MeasureTheory
noncomputable section
open Matrix Polynomial
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution (N m : ℕ) (hm : m ≤ N) (f : Fin N → ℝ) :
    ∑ b : Fin m, f (Fin.castLE hm b) = ∑ k : Fin N, if k.val < m then f k else 0 := by
  rw [← Finset.sum_filter]
  exact Finset.sum_bij (fun b _ => Fin.castLE hm b) (fun b _ => by simp)
    (fun b1 _ b2 _ h => Fin.castLE_injective hm h)
    (fun k hk => ⟨⟨k.val, (Finset.mem_filter.1 hk).2⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    (fun b _ => rfl)
end ReciprocityTheory.AnForm.P
