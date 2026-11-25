-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData.sublevel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:35:06.749155+00:00
-- url     : https://prove2.me/submissions/162f598e-cf3e-4a1d-946c-955f0b674497

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_PolynomialGrowthIntegrals
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_subgroupData_E_closed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData
namespace ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData
theorem _root_.solution (c : Fin 3 → ℂ) {la g : ℝ} (hg : 0 < g)
    (hno : ∀ t1 t2 t3 : ℝ, 1 ≤ t1 → t3 ≤ 2 → g ≤ t2 - t1 → g ≤ t3 - t2 → ‖qv c t1‖ ≤ la →
      ‖qv c t2‖ ≤ la → ‖qv c t3‖ ≤ la → False) :
    volume {t | t ∈ Icc (1:ℝ) 2 ∧ ‖qv c t‖ ≤ la} ≤ ENNReal.ofReal (2 * g) := by
  set E := {t | t ∈ Icc (1:ℝ) 2 ∧ ‖qv c t‖ ≤ la} with hE
  have hcl : IsClosed E := E_closed c la
  have hbdd : BddBelow E := ⟨1, fun t ht => ht.1.1⟩
  rcases E.eq_empty_or_nonempty with h0 | hne
  · rw [h0, measure_empty]; exact bot_le
  set t1 := sInf E with ht1d
  have ht1 : t1 ∈ E := hcl.csInf_mem hne hbdd
  have hge1 : ∀ t ∈ E, t1 ≤ t := fun t ht => csInf_le hbdd ht
  set E2 := E ∩ Ici (t1 + g) with hE2
  rcases E2.eq_empty_or_nonempty with h2 | hne2
  · have hsub : E ⊆ Icc t1 (t1 + g) := by
      intro t ht
      refine ⟨hge1 t ht, ?_⟩
      by_contra hc
      have : t ∈ E2 := ⟨ht, le_of_lt (not_le.mp hc)⟩
      rw [h2] at this; exact this
    calc volume E ≤ volume (Icc t1 (t1 + g)) := measure_mono hsub
      _ = ENNReal.ofReal g := by rw [Real.volume_Icc]; ring_nf
      _ ≤ ENNReal.ofReal (2 * g) := ENNReal.ofReal_le_ofReal (by linarith)
  have hcl2 : IsClosed E2 := hcl.inter isClosed_Ici
  have hbdd2 : BddBelow E2 := ⟨1, fun t ht => ht.1.1.1⟩
  set t2 := sInf E2 with ht2d
  have ht2 : t2 ∈ E2 := hcl2.csInf_mem hne2 hbdd2
  have hge2 : ∀ t ∈ E2, t2 ≤ t := fun t ht => csInf_le hbdd2 ht
  have h12 : t1 + g ≤ t2 := Set.mem_Ici.mp ht2.2
  have hsub : E ⊆ Icc t1 (t1 + g) ∪ Icc t2 (t2 + g) := by
    intro t ht
    by_cases h : t < t1 + g
    · exact Or.inl ⟨hge1 t ht, h.le⟩
    · have htE2 : t ∈ E2 := ⟨ht, not_lt.mp h⟩
      refine Or.inr ⟨hge2 t htE2, ?_⟩
      by_contra hc
      exact hno t1 t2 t ht1.1.1 ht.1.2 (by linarith) (by linarith [not_le.mp hc]) ht1.2 ht2.1.2 ht.2
  calc volume E ≤ volume (Icc t1 (t1 + g) ∪ Icc t2 (t2 + g)) := measure_mono hsub
    _ ≤ volume (Icc t1 (t1 + g)) + volume (Icc t2 (t2 + g)) := measure_union_le _ _
    _ = ENNReal.ofReal (2 * g) := by
        rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_add (by linarith) (by linarith)]
        ring_nf
end ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData
