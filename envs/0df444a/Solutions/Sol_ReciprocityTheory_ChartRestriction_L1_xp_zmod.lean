-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.xp_zmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:46:51.5708+00:00
-- url     : https://prove2.me/submissions/28b3382c-c516-43b0-bf4c-45b0707bd426

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_xp


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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (f : PowerSeries (ZMod p)) : xp p f = f ^ p := by
  haveI := Fact.mk hp
  ext n
  have key := congrArg (fun q => Polynomial.coeff q n) (PowerSeries.trunc_trunc_pow (n := n + 1) f p)
  simp only [PowerSeries.coeff_trunc, Nat.lt_add_one, ↓reduceIte] at key
  rw [← key, ← Polynomial.coe_pow, Polynomial.coeff_coe, ← ZMod.expand_card, Polynomial.coeff_expand hp.pos]
  simp only [xp, PowerSeries.coeff_mk]
  split_ifs with h
  · rw [PowerSeries.coeff_trunc, if_pos (Nat.lt_succ_of_le (Nat.div_le_self n p))]
  · rfl
end ReciprocityTheory.ChartRestriction.L1
