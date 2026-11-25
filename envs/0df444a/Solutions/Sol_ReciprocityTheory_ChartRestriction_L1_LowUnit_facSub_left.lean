-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.LowUnit.facSub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:34:19.610472+00:00
-- url     : https://prove2.me/submissions/54f52aae-a2a1-4034-83a6-a71813e0b4c2

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
    (hf : LowUnit R f n u) (hg : LowUnit R g n' u') (h : n < n') : LowUnit R (f - g) n u := by
  obtain ⟨hu, hui, hu0, hlow, hval⟩ := hf
  obtain ⟨_, _, _, hglow, _⟩ := hg
  refine ⟨hu, hui, hu0, fun k hk => ?_, ?_⟩
  · rw [map_sub, hlow k hk, hglow k (hk.trans h), sub_zero]
  · rw [map_sub, hval, hglow n h, sub_zero]
end LowUnit
end ReciprocityTheory.ChartRestriction.L1
