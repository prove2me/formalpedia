-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.hasUnitLeadingCoeff_rescaleExpand_discriminantSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:18:32.656445+00:00
-- url     : https://prove2.me/submissions/b337a44f-a2f0-4304-9b13-e238cdee5aa9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalMF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFacSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_discriminantSeries_coeff_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_discriminantSeries_coeff_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_sub1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeff_xp


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
theorem _root_.solution {R : Subring ℂ} {c : ℂ} (hc : c ∈ R) (hc' : c⁻¹ ∈ R) (hc0 : c ≠ 0) {k : ℕ}
    (hk : k ≠ 0) : LowUnit R (sub1 c k dC) k c := by
  refine ⟨hc, hc', hc0, fun n hn => ?_, ?_⟩
  · rw [sub1, coeff_xp]
    split_ifs with hd
    · have h0 : n = 0 := Nat.eq_zero_of_dvd_of_lt hd hn
      subst h0
      rw [Nat.zero_div, PowerSeries.coeff_rescale, discriminantSeries_coeff_zero, mul_zero]
    · rfl
  · rw [sub1, coeff_xp, if_pos dvd_rfl, Nat.div_self (Nat.pos_of_ne_zero hk), PowerSeries.coeff_rescale,
      pow_one, discriminantSeries_coeff_one, mul_one]
end ReciprocityTheory.ChartRestriction.L1
