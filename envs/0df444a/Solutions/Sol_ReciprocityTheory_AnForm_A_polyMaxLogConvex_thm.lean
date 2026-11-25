-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.polyMaxLogConvex_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:19:10.351547+00:00
-- url     : https://prove2.me/submissions/faa14a12-2fd2-4934-9f9e-09fcfbe0302a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_polyMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_polyMax_attained
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_mono__555a93f5b347
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_zero__254d90a70d0d
import Theorems.Thm_ReciprocityTheory_AnForm_A_polyMax_usc
import Theorems.Thm_ReciprocityTheory_AnForm_A_chord_to_convex
import Theorems.Thm_ReciprocityTheory_AnForm_A_polydiscMax_exp_chord_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : PolyMaxLogConvexStatement := by
  intro D U φ z R hU hφ hR0 hR
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine chord_to_convex (convex_Iic _) fun x hx y hy hxy α β hx' hy' p hp => ?_
    refine le_of_forall_pos_le_add fun e he => ?_
    have hB : 0 < Real.exp y ^ 2 + 1 := by positivity
    have key := polydiscMax_exp_chord_bound hU hφ hR0 hR hxy hy hx' hy' (div_pos he hB) hp
    have h2 : e / (Real.exp y ^ 2 + 1) * Real.exp y ^ 2 ≤ e := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hB]; nlinarith
    have h3 : 0 ≤ e / (Real.exp y ^ 2 + 1) * Real.exp p ^ 2 := by positivity
    linarith
  · exact fun s hs t ht hst =>
      polyMax_mono' hφ.1 hs.1.le hst ((closedBall_subset_closedBall ht.2).trans hR)
  · exact fun t ht0 htR => polyMax_attained hφ.1 ht0 ((closedBall_subset_closedBall htR).trans hR)
  · have h0U : closedBall z 0 ⊆ U := (closedBall_subset_closedBall hR0.le).trans hR
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hR0)] with t ht htR
      have hsub : closedBall z t ⊆ U :=
        (closedBall_subset_closedBall (le_of_lt htR)).trans hR
      have := le_polyMax hφ.1 hsub (mem_closedBall_self (le_of_lt ht))
      linarith
    · obtain ⟨δ, hδ, -, hδ'⟩ := polyMax_usc hU hφ.1 le_rfl h0U (sub_pos.2 ha)
      rw [polyMax_zero'] at hδ'
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with t ht htδ
      have := hδ' t (le_of_lt ht) (by simp only [zero_add]; exact le_of_lt htδ)
      linarith
end ReciprocityTheory.AnForm.A
