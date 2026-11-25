-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.LowUnit.facSub_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:34:24.967886+00:00
-- url     : https://prove2.me/submissions/1ad94614-dd61-47de-a249-a3808b766cf7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalMF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFacSer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
namespace LowUnit
theorem _root_.solution {R : Subring ℂ} {f g : PowerSeries ℂ} {n n' : ℕ} {u u' : ℂ}
    (hf : LowUnit R f n u) (hg : LowUnit R g n' u') (h : n' < n) : LowUnit R (f - g) n' (-u') := by
  obtain ⟨_, _, _, hflow, _⟩ := hf
  obtain ⟨hu, hui, hu0, hglow, hval⟩ := hg
  refine ⟨neg_mem hu, by rw [inv_neg]; exact neg_mem hui, neg_ne_zero.2 hu0, fun k hk => ?_, ?_⟩
  · rw [map_sub, hflow k (hk.trans h), hglow k hk, sub_zero]
  · rw [map_sub, hflow n' h, hval, zero_sub]
end LowUnit
end ReciprocityTheory.ChartRestriction.L1
