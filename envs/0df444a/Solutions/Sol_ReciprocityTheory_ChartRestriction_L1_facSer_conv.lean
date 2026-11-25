-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.facSer_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:06:54.648837+00:00
-- url     : https://prove2.me/submissions/78a913b0-072b-4833-ae8f-8a93384a542c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalMF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFacSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_zetaRoot_pow_of_mem_hermiteTriples
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_convergesOnDisk_eisensteinFourCubeSeries
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_convergesOnDisk_discriminantSeries
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_sub1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_xp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LowUnit_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
namespace ReciprocityTheory.ChartRestriction.L1
private theorem dvd_and_eq_div_of_mem_Tm {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) :
    t.1 ∣ m ∧ 0 < t.1 ∧ t.2.2 = m / t.1 ∧ t.1 * t.2.2 = m := by
  simp only [Tm, Finset.mem_image, Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range] at ht
  obtain ⟨⟨a, b⟩, ⟨⟨hdvd, _⟩, _⟩, rfl⟩ := ht
  exact ⟨hdvd, Nat.pos_of_dvd_of_pos hdvd hm, rfl, Nat.mul_div_cancel' hdvd⟩
end ReciprocityTheory.ChartRestriction.L1
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) : Conv (facSer m t) := by
  have hc : ‖zetaC t.2.2 ^ t.2.1‖ ≤ 1 := (norm_zetaRoot_pow_of_mem_hermiteTriples hm ht).le
  have hk : t.1 ^ 2 ≠ 0 := pow_ne_zero _ (dvd_and_eq_div_of_mem_Tm hm ht).2.1.ne'
  unfold facSer
  exact ((convergesOnDisk_eisensteinFourCubeSeries.xp hm.ne').mul (convergesOnDisk_discriminantSeries.sub1 hc hk)).sub
    ((convergesOnDisk_eisensteinFourCubeSeries.sub1 hc hk).mul (convergesOnDisk_discriminantSeries.xp hm.ne'))
end ReciprocityTheory.ChartRestriction.L1
