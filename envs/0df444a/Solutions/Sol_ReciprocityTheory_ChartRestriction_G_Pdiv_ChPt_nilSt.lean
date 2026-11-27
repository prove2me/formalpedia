-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt.nilSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:33:43.399778+00:00
-- url     : https://prove2.me/submissions/df744227-0a2e-4f71-9bac-7665525efbe5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ChartPointCongruence_InChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ChartPointCongruence_EqOfMod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open ReciprocityTheory.ChartRestriction.G.Chart (jetLift jetLift_zR jet_ext)
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
theorem _root_.solution : NilSt := by
  intro p hp C _ _ v O _ _ hv _ hpu c hc n
  have hunit : ∀ x : O, ¬ IsUnit x → v (algebraMap O C x) < 1 := by
    intro x hx
    refine lt_of_le_of_ne (hv.map_le_one x) ?_
    intro h1
    apply hx
    refine hv.isUnit_of_one ?_ h1
    refine isUnit_iff_ne_zero.mpr ?_
    intro h0
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  have hc1 : v (algebraMap O C c) < 1 := by
    apply hunit c
    intro hu
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top (Ideal.eq_top_of_isUnit_mem _ hc hu)
  have hp0 : 0 < v (algebraMap O C ((p : O) ^ n)) := by
    rw [map_pow, map_pow, map_natCast]
    apply pow_pos
    rw [pos_iff_ne_zero, Ne, Valuation.zero_iff]
    exact Nat.cast_ne_zero.mpr hp
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hp0 hc1
  refine ⟨N, Ideal.mem_span_singleton.mpr (hv.dvd_of_le ?_)⟩
  have e : v (algebraMap O C (c ^ N)) = v (algebraMap O C c) ^ N := by
    rw [map_pow, map_pow]
  rw [e]
  exact hN.le
end ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
