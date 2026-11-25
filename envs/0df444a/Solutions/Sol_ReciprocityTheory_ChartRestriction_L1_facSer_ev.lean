-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.facSer_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:18:27.130298+00:00
-- url     : https://prove2.me/submissions/30d263a1-7dfb-4300-ad51-a03c52b1ff4e

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_evalSeries_eisensteinFourCubeSeries
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_evalSeries_discriminantSeries
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_sub1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_xp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LowUnit_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ev_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ev_xp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_evalSeries_rescaleExpand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_qm_norm_lt_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_qm_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_qm_pt

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
theorem _root_.solution {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) (τ : ℍ) :
    ev (facSer m t) (qm m τ) = fac t τ := by
  obtain ⟨hdvd, ha0, he, hae⟩ := dvd_and_eq_div_of_mem_Tm hm ht
  have he0 : 0 < t.2.2 := by
    rw [he]
    exact Nat.div_pos (Nat.le_of_dvd hm hdvd) ha0
  have hq := qm_norm_lt_one hm τ
  have hc := (norm_zetaRoot_pow_of_mem_hermiteTriples hm ht).le
  have hk : t.1 ^ 2 ≠ 0 := pow_ne_zero _ ha0.ne'
  have hA := convergesOnDisk_eisensteinFourCubeSeries
  have hD := convergesOnDisk_discriminantSeries
  have hpt : zetaC t.2.2 ^ t.2.1 * qm m τ ^ (t.1 ^ 2) = qm 1 (pt t.1 t.2.1 t.2.2 τ) := by
    rw [qm_pt ha0 he0, hae]
  unfold facSer fac
  rw [ev_sub ((hA.xp hm.ne').mul (hD.sub1 hc hk)) ((hA.sub1 hc hk).mul (hD.xp hm.ne')) hq,
    ev_mul (hA.xp hm.ne') (hD.sub1 hc hk) hq, ev_mul (hA.sub1 hc hk) (hD.xp hm.ne') hq,
    ev_xp _ hm.ne', ev_xp _ hm.ne', evalSeries_rescaleExpand _ _ hk, evalSeries_rescaleExpand _ _ hk, qm_pow hm, hpt]
  simp only [evalSeries_eisensteinFourCubeSeries, evalSeries_discriminantSeries]
end ReciprocityTheory.ChartRestriction.L1
