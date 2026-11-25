-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.disc_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:51:09.907479+00:00
-- url     : https://prove2.me/submissions/add9c860-eda4-4baa-9684-e72f75f3a0a8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DiscSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_CauchyInequalityOnTorus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DiscPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_disc_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution : DiscStatement := by
  intro K _ _ _ K₀ hres S hS hdense c b hb hc n
  have hbd : ∀ t ∈ S, ‖c n‖ * ‖t‖ ^ n ≤ 1 := fun t ht => disc_bound K₀ hres c S hc t ht n
  constructor
  · by_contra hlt
    push_neg at hlt
    have hcont : ContinuousAt (fun x : ℝ => ‖c n‖ * x ^ n) 1 :=
      continuousAt_const.mul (continuousAt_zpow₀ (1 : ℝ) n (Or.inl one_ne_zero))
    have hev : ∀ᶠ x in nhds (1 : ℝ), 1 < ‖c n‖ * x ^ n :=
      hcont.eventually (lt_mem_nhds (by simpa using hlt))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set r : ℝ := max (1 / 2) (1 - ε / 2) with hr
    have hr0 : 0 < r := lt_max_of_lt_left (by norm_num)
    have hr1 : r < 1 := max_lt (by norm_num) (by linarith)
    obtain ⟨t, htS, ht⟩ :=
      hdense r hr0 hr1 (min (ε / 2) (1 - r)) (lt_min (by linarith) (by linarith))
    have h1 := hbd t htS
    have h2 := (hS t htS).2
    have hdist : dist ‖t‖ 1 < ε := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith : (0 : ℝ) < 1 - ‖t‖)]
      have h4 := (abs_lt.1 ht).1
      have h5 : min (ε / 2) (1 - r) ≤ ε / 2 := min_le_left _ _
      have h3 : 1 - ε / 2 ≤ r := le_max_right _ _
      linarith
    exact absurd h1 (not_le.2 (hball hdist))
  · intro hn
    by_contra hne
    have hq : 0 < ‖c n‖ := norm_pos_iff.2 hne
    have hm : 0 < -n := by omega
    have hcont : ContinuousAt (fun x : ℝ => x ^ (-n)) 0 :=
      continuousAt_zpow₀ (0 : ℝ) (-n) (Or.inr hm.le)
    have h0 : (fun x : ℝ => x ^ (-n)) 0 = 0 := zero_zpow _ hm.ne'
    have hev : ∀ᶠ x in nhds (0 : ℝ), x ^ (-n) < ‖c n‖ :=
      hcont.eventually (gt_mem_nhds (by rw [h0]; exact hq))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set r : ℝ := min (1 / 2) (ε / 2) with hr
    have hr0 : 0 < r := lt_min (by norm_num) (by linarith)
    have hr1 : r < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    obtain ⟨t, htS, ht⟩ := hdense r hr0 hr1 r hr0
    have htpos := (hS t htS).1
    have hdist : dist ‖t‖ 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
      have h4 := (abs_lt.1 ht).2
      have h5 : r ≤ ε / 2 := min_le_right _ _
      linarith
    have h6 := hball hdist
    have h1 := hbd t htS
    have h7 : ‖t‖ ^ n * ‖t‖ ^ (-n) = 1 := by
      rw [← zpow_add₀ htpos.ne', add_neg_cancel, zpow_zero]
    have h9 : ‖c n‖ ≤ ‖t‖ ^ (-n) := by
      have h10 := mul_le_mul_of_nonneg_right h1 (zpow_pos htpos (-n)).le
      rw [mul_assoc, h7, mul_one, one_mul] at h10
      exact h10
    linarith
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
