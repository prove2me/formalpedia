-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.sub_pow_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:47:45.758017+00:00
-- url     : https://prove2.me/submissions/f2632051-dcbc-43e2-bc50-3b95c159cead

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_exists_C_mul_of_map_eq_zero

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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (f g : PowerSeries ℤ) :
    ∃ w : PowerSeries ℤ, (f - g) ^ p = f ^ p - g ^ p + PowerSeries.C (p : ℤ) * w := by
  haveI := Fact.mk hp
  haveI : CharP (PowerSeries (ZMod p)) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (PowerSeries (ZMod p))).injective p
  have h0 : ((f - g) ^ p - (f ^ p - g ^ p)).map (Int.castRingHom (ZMod p)) = 0 := by
    rw [map_sub, map_pow, map_sub, map_sub, map_pow, map_pow, sub_pow_char, sub_self]
  obtain ⟨w, hw⟩ := exists_C_mul_of_map_eq_zero (p := p) _ h0
  exact ⟨w, by rw [← hw]; ring⟩
end ReciprocityTheory.ChartRestriction.L1
