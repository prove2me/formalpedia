-- Prove2me | solution 1 for ReciprocityTheory.Cheb.bounded_of_tendsto_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:58:02.1441+00:00
-- url     : https://prove2.me/submissions/347b9af1-57d8-49a1-93b6-a535bc4a9a53

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_NoWind
import Theorems.Thm_ReciprocityTheory_Cheb_isDiscrete_exp_fiber

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Cheb
open Filter Topology Set Complex
namespace ReciprocityTheory.Cheb
theorem _root_.solution {abelian₂ : ℝ → ℂ} {L1 : ℂ} (hcont : ContinuousOn abelian₂ (Ioc 1 2))
    (hL1 : L1 ≠ 0) (hlim : Tendsto (fun s => Complex.exp (abelian₂ s)) (𝓝[>] 1) (𝓝 L1)) :
    ∃ C, ∀ s ∈ Ioc (1 : ℝ) 2, ‖abelian₂ s‖ ≤ C := by

  have hslitB : ∀ z ∈ Metric.closedBall (1 : ℂ) (1 / 2), z ∈ slitPlane := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have := Complex.abs_re_le_norm (z - 1)
    rw [Complex.sub_re, Complex.one_re] at this
    exact mem_slitPlane_iff.mpr (Or.inl (by linarith [(abs_le.mp (this.trans hz)).1]))
  obtain ⟨B, hB⟩ := (isCompact_closedBall (1 : ℂ) (1 / 2)).exists_bound_of_continuousOn
    (f := Complex.log) (fun z hz => (continuousAt_clog (hslitB z hz)).continuousWithinAt)

  have hlim' : Tendsto (fun s => Complex.exp (abelian₂ s) / L1) (𝓝[>] 1) (𝓝 1) := by
    simpa [div_self hL1] using hlim.div_const L1
  have hev := hlim'.eventually (Metric.closedBall_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨u, hu1, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hu1 : (1 : ℝ) < u := hu1
  set t : ℝ := min ((1 + u) / 2) 2 with ht
  have ht1 : 1 < t := lt_min (by linarith) (by norm_num)
  have htu : t < u := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht2 : t ≤ 2 := min_le_right _ _
  have hSsub : Ioc 1 t ⊆ Ioc (1 : ℝ) 2 := Ioc_subset_Ioc_right ht2
  have hball : ∀ s ∈ Ioc 1 t, Complex.exp (abelian₂ s) / L1 ∈ Metric.closedBall (1 : ℂ) (1 / 2) :=
    fun s hs => hu ⟨hs.1, lt_of_le_of_lt hs.2 htu⟩

  set g : ℝ → ℂ := fun s => abelian₂ s - Complex.log (Complex.exp (abelian₂ s) / L1) with hg
  have hgc : ContinuousOn g (Ioc 1 t) := by
    intro s hs
    have h1 : ContinuousWithinAt abelian₂ (Ioc 1 t) s := (hcont s (hSsub hs)).mono hSsub
    have h2 : ContinuousWithinAt (fun s => Complex.exp (abelian₂ s) / L1) (Ioc 1 t) s :=
      (Complex.continuous_exp.continuousAt.comp_continuousWithinAt h1).div_const L1
    have h3 : ContinuousWithinAt (fun s => Complex.log (Complex.exp (abelian₂ s) / L1)) (Ioc 1 t) s :=
      (continuousAt_clog (hslitB _ (hball s hs))).comp_continuousWithinAt
        (f := fun s => Complex.exp (abelian₂ s) / L1) h2
    exact h1.sub h3
  have hmaps : MapsTo g (Ioc 1 t) {w : ℂ | Complex.exp w = L1} := by
    intro s _
    have hne : Complex.exp (abelian₂ s) / L1 ≠ 0 := div_ne_zero (Complex.exp_ne_zero _) hL1
    simp only [mem_ofPred_eq, hg, Complex.exp_sub, Complex.exp_log hne]
    field_simp [Complex.exp_ne_zero]
  obtain ⟨c, -, hc⟩ := isPreconnected_Ioc.eqOn_const_of_mapsTo (isDiscrete_exp_fiber L1) hgc hmaps
    ⟨Complex.log L1, Complex.exp_log hL1⟩

  obtain ⟨C2, hC2⟩ := (isCompact_Icc : IsCompact (Icc t 2)).exists_bound_of_continuousOn
    (hcont.mono (Icc_subset_Ioc_iff ht2 |>.mpr ⟨ht1, le_rfl⟩))
  refine ⟨max (‖c‖ + B) C2, fun s hs => ?_⟩
  rcases le_or_gt s t with hst | hst
  · have hs' : s ∈ Ioc 1 t := ⟨hs.1, hst⟩
    have hgs : g s = c := hc hs'
    have hL : abelian₂ s = c + Complex.log (Complex.exp (abelian₂ s) / L1) := by
      rw [← hgs, hg]; ring
    calc ‖abelian₂ s‖ = ‖c + Complex.log (Complex.exp (abelian₂ s) / L1)‖ := by rw [← hL]
      _ ≤ ‖c‖ + ‖Complex.log (Complex.exp (abelian₂ s) / L1)‖ := norm_add_le _ _
      _ ≤ ‖c‖ + B := by gcongr; exact hB _ (hball s hs')
      _ ≤ _ := le_max_left _ _
  · exact (hC2 s ⟨hst.le, hs.2⟩).trans (le_max_right _ _)
end ReciprocityTheory.Cheb
