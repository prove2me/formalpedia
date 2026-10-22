-- Prove2me | solution 1 for ProcessingNetworks.GlobalStability.reentrant_line_globally_stable_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:54:46.039766+00:00
-- url     : https://prove2.me/submissions/a857c43d-8197-4b83-adef-b871bdf2a553

import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_GlobalStability_NonIdlingFluidModel
import Definitions.Def_ProcessingNetworks_GlobalStability_ReentrantLine

open MeasureTheory Filter Topology Set

namespace ProcessingNetworks.GlobalStability

noncomputable def rgDini (f : ℝ → ℝ) (t : ℝ) : EReal :=
  Filter.limsup (fun h : ℝ => (((f (t + h) - f t) / h : ℝ) : EReal))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

theorem rgd_dini_of_hasDerivAt (f : ℝ → ℝ) (d t : ℝ) (h : HasDerivAt f d t) :
    rgDini f t = (d : EReal) := by
  have h1 := h.tendsto_slope_zero_right
  have h2 : Tendsto (fun s : ℝ => (((f (t + s) - f t) / s : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (d : EReal)) :=
    (continuous_coe_real_ereal.tendsto d).comp (h1.congr fun s => by
      simp [smul_eq_mul, div_eq_inv_mul])
  exact h2.limsup_eq

theorem rgd_freq (f : ℝ → ℝ) (x M : ℝ) (hD : rgDini f x ≤ (M : EReal)) (r : ℝ)
    (hr : M < r) : ∃ᶠ z in 𝓝[>] x, slope f x z < r := by
  have hlt : rgDini f x < (r : EReal) := lt_of_le_of_lt hD (EReal.coe_lt_coe_iff.mpr hr)
  have e : ∀ᶠ h in 𝓝[>] (0 : ℝ), (((f (x + h) - f x) / h : ℝ) : EReal) < (r : EReal) :=
    eventually_lt_of_limsup_lt hlt
  have ht : Tendsto (fun z : ℝ => z - x) (𝓝[>] x) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun z : ℝ => z - x) (𝓝 x) (𝓝 (x - x)) :=
        ((continuous_id.sub continuous_const).tendsto x)
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact sub_pos.mpr (show x < z from hz)
  refine (ht.eventually e).mono (fun z hz => ?_) |>.frequently
  rw [slope_def_field]
  simp only [add_sub_cancel] at hz
  exact EReal.coe_lt_coe_iff.mp hz

theorem rgd_upper (f : ℝ → ℝ) (a b M : ℝ) (hc : ContinuousOn f (Icc a b))
    (hD : ∀ t ∈ Ico a b, rgDini f t ≤ (M : EReal)) :
    ∀ x ∈ Icc a b, f x ≤ f a + M * (x - a) := by
  intro x hx
  refine le_of_forall_pos_le_add fun η hη => ?_
  set δ := η / (x - a + 1) with hδ
  have hxa : 0 ≤ x - a := sub_nonneg.mpr hx.1
  have hδpos : 0 < δ := by positivity
  have key := image_le_of_liminf_slope_right_lt_deriv_boundary' (f' := fun _ => M) hc
    (fun t ht r hr => rgd_freq f t M (hD t ht) r hr)
    (B := fun t => f a + (M + δ) * (t - a)) (B' := fun _ => M + δ) (by simp)
    (by fun_prop)
    (fun t _ => (((hasDerivAt_id t).sub_const a).const_mul (M + δ)).const_add (f a)
      |>.hasDerivWithinAt |>.congr_deriv (by simp))
    (fun t _ _ => by linarith) hx
  have : δ * (x - a) ≤ η := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

theorem rgd_mono (f : ℝ → ℝ) (a b M : ℝ) (hc : ContinuousOn f (Icc a b))
    (hD : ∀ t ∈ Ico a b, rgDini f t ≤ (M : EReal)) :
    MonotoneOn (fun t => M * t - f t) (Icc a b) := by
  intro x hx y hy hxy
  have := rgd_upper f x y M (hc.mono (Icc_subset_Icc hx.1 hy.2))
    (fun t ht => hD t ⟨hx.1.trans ht.1, lt_of_lt_of_le ht.2 hy.2⟩) y ⟨hxy, le_rfl⟩
  simp only
  linarith

theorem rgd_decrease (f : ℝ → ℝ) (a b M ε : ℝ) (ha : 0 < a) (hab : a < b)
    (hc : ContinuousOn f (Icc a b))
    (hD : ∀ t ∈ Ico a b, rgDini f t ≤ (M : EReal))
    (hpos : ∀ t ∈ Ioo a b, 0 < f t)
    (hdrift : ∀ᵐ t, 0 ≤ t → 0 < f t → rgDini f t ≤ ((-ε : ℝ) : EReal)) :
    f b ≤ f a - ε * (b - a) := by
  set h : ℝ → ℝ := fun t => M * t - f t with hh
  have hmono : MonotoneOn h (Icc a b) := rgd_mono f a b M hc hD
  have hmono' : MonotoneOn h (uIcc a b) := by rwa [uIcc_of_le hab.le]
  have hint := hmono'.intervalIntegral_deriv_mem_uIcc
  have hhab : 0 ≤ h b - h a := sub_nonneg.mpr (hmono ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab.le)
  rw [uIcc_of_le hhab] at hint
  have hii := hmono'.intervalIntegrable_deriv
  have hfin : ({a, b} : Set ℝ).Finite := by simp
  have hae : ∀ᵐ x, x ∈ ({a, b} : Set ℝ)ᶜ := compl_mem_ae_iff.mpr (hfin.measure_zero _)
  have hlow : (fun _ => M + ε) ≤ᵐ[volume.restrict (Icc a b)] deriv h := by
    show ∀ᵐ x ∂(volume.restrict (Icc a b)), M + ε ≤ deriv h x
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hmono.ae_differentiableWithinAt_of_mem, hdrift, hae] with x hd hdr hne hx
    have hxa : x ≠ a := fun e => hne (by simp [e])
    have hxb : x ≠ b := fun e => hne (by simp [e])
    have hxI : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
    have hdiff : DifferentiableAt ℝ h x := (hd hx).differentiableAt (Icc_mem_nhds hxI.1 hxI.2)
    have hfeq : f = fun t => M * t - h t := by funext t; simp [hh]
    have hfd : HasDerivAt f (M - deriv h x) x := by
      rw [hfeq]
      have := ((hasDerivAt_id x).const_mul M).sub hdiff.hasDerivAt
      simp only [mul_one, id] at this
      exact this
    have := hdr (ha.le.trans hx.1) (hpos x hxI)
    rw [rgd_dini_of_hasDerivAt f _ x hfd, EReal.coe_le_coe_iff] at this
    show M + ε ≤ deriv h x
    linarith
  have hmono_int := intervalIntegral.integral_mono_ae_restrict hab.le
    intervalIntegrable_const hii hlow
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hmono_int
  have := hint.2
  simp only [hh] at this
  nlinarith

theorem rgd_induct (f : ℝ → ℝ) (hcont : ContinuousOn f (Ioi 0))
    (hbound : ∀ a b : ℝ, 0 ≤ a → a < b → ∃ M : ℝ, 0 < M ∧ ∀ t ∈ Ico a b, rgDini f t ≤ (M : EReal))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hdrift : ∀ᵐ t, 0 ≤ t → 0 < f t → rgDini f t ≤ ((-ε : ℝ) : EReal))
    (a δ C : ℝ) (ha : 0 < a) (hδ : 0 < δ) (h0 : f a ≤ max δ (C - ε * a)) :
    ∀ x, a ≤ x → f x ≤ max δ (C - ε * x) := by
  intro x hx
  set g : ℝ → ℝ := fun y => max δ (C - ε * y) with hg
  have hgc : Continuous g := by fun_prop
  have hfc : ∀ y, 0 < y → ContinuousAt f y := fun y hy =>
    hcont.continuousAt (isOpen_Ioi.mem_nhds hy)
  have hsub : Icc a x ⊆ {y | f y ≤ g y} := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin ?_ h0 ?_
    · have hcI : ContinuousOn (fun y => g y - f y) (Icc a x) :=
        hgc.continuousOn.sub (hcont.mono fun y hy => lt_of_lt_of_le ha hy.1)
      have := hcI.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Ici (a := (0 : ℝ)))
      convert this using 1
      ext y; simp [and_comm]
    · rintro y ⟨hy, hyI⟩
      have hy0 : 0 < y := lt_of_lt_of_le ha hyI.1
      rcases lt_or_eq_of_le (show f y ≤ g y from hy) with hlt | heq
      · have : ∀ᶠ z in 𝓝 y, f z < g z :=
          ((hgc.continuousAt.sub (hfc y hy0)).eventually (lt_mem_nhds (sub_pos.mpr hlt))).mono
            fun z hz => sub_pos.mp hz
        exact mem_nhdsWithin_of_mem_nhds (this.mono fun z hz => le_of_lt hz)
      · have hfy : 0 < f y := lt_of_lt_of_le hδ (heq ▸ le_max_left _ _)
        have hev : ∀ᶠ z in 𝓝 y, 0 < f z := (hfc y hy0).eventually (lt_mem_nhds hfy)
        obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hev
        refine mem_of_superset (Ioo_mem_nhdsGT (show y < y + η by linarith)) fun z hz => ?_
        obtain ⟨M, -, hM⟩ := hbound y z hy0.le hz.1
        have hdec := rgd_decrease f y z M ε hy0 hz.1
          (hcont.mono fun w hw => lt_of_lt_of_le hy0 hw.1) hM
          (fun w hw => hball (by
            rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hw.1, hw.2, hz.2]))
          hdrift
        show f z ≤ g z
        rw [heq] at hdec
        simp only [hg] at hdec ⊢
        rcases le_total δ (C - ε * y) with hm | hm
        · rw [max_eq_right hm] at hdec
          exact le_trans (by linarith) (le_max_right _ _)
        · rw [max_eq_left hm] at hdec
          have : 0 ≤ ε * (z - y) := mul_nonneg hε (by linarith [hz.1])
          exact le_trans (by linarith) (le_max_left _ _)
  exact hsub ⟨hx, le_rfl⟩


theorem rgd_extinction
    (f : ℝ → ℝ) (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t)
    (hcont : ContinuousOn f (Set.Ioi 0))
    (hbound : ∀ a b : ℝ, 0 ≤ a → a < b → ∃ M : ℝ, 0 < M ∧ ∀ t ∈ Set.Ico a b, rgDini f t ≤ (M : EReal))
    (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ᵐ t, 0 ≤ t → 0 < f t → rgDini f t ≤ ((-ε : ℝ) : EReal)) :
    ∀ t : ℝ, f 0 / ε ≤ t → f t = 0 := by
  intro t ht
  have hf0 := hnonneg 0 le_rfl
  have ht0 : 0 ≤ t := le_trans (div_nonneg hf0 hε.le) ht
  have hft : f 0 ≤ ε * t := by rwa [div_le_iff₀ hε, mul_comm] at ht
  refine le_antisymm ?_ (hnonneg t ht0)
  rcases eq_or_lt_of_le ht0 with h0 | htpos
  · subst h0; linarith
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨M0, hM0, hD0⟩ := hbound 0 1 le_rfl one_pos
  have hD : rgDini f 0 < ((M0 + 1 : ℝ) : EReal) :=
    lt_of_le_of_lt (hD0 0 ⟨le_rfl, one_pos⟩) (EReal.coe_lt_coe_iff.mpr (by linarith))
  have e1 : ∀ᶠ h in 𝓝[>] (0 : ℝ), (((f (0 + h) - f 0) / h : ℝ) : EReal) < ((M0 + 1 : ℝ) : EReal) :=
    eventually_lt_of_limsup_lt hD
  set K := M0 + 1 + ε with hK
  have hKpos : 0 < K := by linarith
  set c := min t (η / (2 * K)) with hc
  have hcpos : 0 < c := lt_min htpos (by positivity)
  obtain ⟨a, ha1, ha2⟩ := (e1.and (Ioo_mem_nhdsGT hcpos)).exists
  have hapos : 0 < a := ha2.1
  rw [EReal.coe_lt_coe_iff, zero_add, div_lt_iff₀ hapos] at ha1
  have hfa : f a ≤ max (η / 2) (f 0 + (M0 + 1) * a + ε * a - ε * a) :=
    le_trans (by linarith) (le_max_right _ _)
  have key := rgd_induct f hcont hbound ε hε.le hdrift a (η / 2) (f 0 + (M0 + 1) * a + ε * a) hapos
    (by positivity) hfa t (le_trans ha2.2.le (min_le_left _ _))
  have hac : a * K ≤ η / 2 := by
    have : a ≤ η / (2 * K) := le_trans ha2.2.le (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have : f 0 + (M0 + 1) * a + ε * a - ε * t ≤ η / 2 := by nlinarith
  have := max_le (le_refl (η / 2)) this
  linarith


theorem rg_dini_le (f : ℝ → ℝ) (t c : ℝ)
    (h : ∀ᶠ s in 𝓝[>] (0:ℝ), f (t + s) - f t ≤ c * s) : rgDini f t ≤ (c : EReal) := by
  unfold rgDini
  refine Filter.limsup_le_of_le (h := ?_)
  filter_upwards [h, self_mem_nhdsWithin] with s hs hs0
  have hs0' : (0:ℝ) < s := hs0
  rw [EReal.coe_le_coe_iff, div_le_iff₀ hs0']
  linarith


theorem rl_pool_sum (lam1 m1 m2 m3 m4 m5 : ℝ) (g : Fin 5 → ℝ) (k : Fin 2) :
    ∑ i ∈ poolBuffers (reentrantLineData lam1 m1 m2 m3 m4 m5) k, g i
      = ![g 0 + g 2 + g 4, g 1 + g 3] k := by
  unfold poolBuffers
  rw [Finset.sum_filter, Fin.sum_univ_five]
  fin_cases k <;> simp [reentrantLineData] <;> ring

theorem rl_route_sum (lam1 m1 m2 m3 m4 m5 : ℝ) (F : Fin 5 → ℝ) (i : Fin 5) :
    ∑ j, (reentrantLineData lam1 m1 m2 m3 m4 m5).P j i * F j = ![0, F 0, F 1, F 2, F 3] i := by
  fin_cases i <;> simp [reentrantLineData, Fin.sum_univ_five]

theorem rl_m (lam1 m1 m2 m3 m4 m5 : ℝ) : (reentrantLineData lam1 m1 m2 m3 m4 m5).m = ![m1, m2, m3, m4, m5] := rfl
theorem rl_lam (lam1 m1 m2 m3 m4 m5 : ℝ) : (reentrantLineData lam1 m1 m2 m3 m4 m5).lam = ![lam1, 0, 0, 0, 0] := rfl
theorem rl_b (lam1 m1 m2 m3 m4 m5 : ℝ) : (reentrantLineData lam1 m1 m2 m3 m4 m5).b = ![1, 1] := rfl

theorem rl_deriv_nonneg_of_mono (g : ℝ → ℝ) (hg : Monotone g) (d t : ℝ) (h : HasDerivAt g d t) :
    0 ≤ d := by
  have := h.tendsto_slope_zero_right
  refine ge_of_tendsto this ?_
  filter_upwards [self_mem_nhdsWithin] with h' hh'
  have h0 : (0:ℝ) < h' := hh'
  rw [smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr h0.le) (sub_nonneg.mpr (hg (by linarith)))

set_option maxHeartbeats 0 in
/-- Sufficiency: the three conditions imply global stability. -/
theorem rl_stable_of_conditions (lam1 m1 m2 m3 m4 m5 : ℝ) (hlam1 : 0 < lam1)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm3 : 0 < m3) (hm4 : 0 < m4) (hm5 : 0 < m5)
    (x1 x2 x3 x4 x5 : ℝ) (hx5 : 0 < x5) (h54 : x5 < x4) (h435 : x4 < x3 + x5)
    (h2435 : x3 + x5 < x2 + x4) (hS : x2 + x4 < x1 + x3 + x5)
    (b1 : lam1 * (x1 + x3 + x5) * m1 < x1) (b3 : lam1 * (x1 + x3 + x5) * m3 < x3)
    (b5 : lam1 * (x1 + x3 + x5) * m5 < x5)
    (b2 : lam1 * (x2 + x4) * m2 < x2) (b4 : lam1 * (x2 + x4) * m4 < x4) :
    FluidModelGloballyStable (reentrantLineData lam1 m1 m2 m3 m4 m5) := by
  set S1 := x1 + x3 + x5 with hS1
  set S2 := x2 + x4 with hS2
  have hS1pos : 0 < S1 := by
    by_contra hcon
    push Not at hcon
    have : lam1 * S1 * (m1 + m3 + m5) < S1 := by linarith
    nlinarith [mul_nonneg (mul_nonneg hlam1.le (by linarith : (0:ℝ) ≤ -S1)) (by linarith : (0:ℝ) ≤ m1 + m3 + m5)]
  have hx1 : 0 < x1 := lt_of_le_of_lt (by positivity) b1
  have hx3 : 0 < x3 := lt_of_le_of_lt (by positivity) b3
  have hS2pos : 0 < S2 := by linarith
  have hx2 : 0 < x2 := lt_of_le_of_lt (by positivity) b2
  have hx4 : 0 < x4 := lt_of_le_of_lt (by positivity) b4
  -- the margins
  set ε := min (min (min (x1 / m1 - lam1 * S1) (x3 / m3 - lam1 * S1)) (x5 / m5 - lam1 * S1))
    (min (x2 / m2 - lam1 * S2) (x4 / m4 - lam1 * S2)) with hε
  have e1 : lam1 * S1 + ε ≤ x1 / m1 := by
    have : ε ≤ x1 / m1 - lam1 * S1 := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
    linarith
  have e3 : lam1 * S1 + ε ≤ x3 / m3 := by
    have : ε ≤ x3 / m3 - lam1 * S1 := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
    linarith
  have e5 : lam1 * S1 + ε ≤ x5 / m5 := by
    have : ε ≤ x5 / m5 - lam1 * S1 := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have e2 : lam1 * S2 + ε ≤ x2 / m2 := by
    have : ε ≤ x2 / m2 - lam1 * S2 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have e4 : lam1 * S2 + ε ≤ x4 / m4 := by
    have : ε ≤ x4 / m4 - lam1 * S2 := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have hεpos : 0 < ε := by
    rw [hε]
    refine lt_min (lt_min (lt_min ?_ ?_) ?_) (lt_min ?_ ?_) <;> rw [sub_pos, lt_div_iff₀ (by assumption)]
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
  set M := lam1 * (S1 + S2) with hM
  have hMpos : 0 < M := by positivity
  refine ⟨2 * (S1 + S2) / ε, by positivity, fun Dh Fh Th Zh hsol t ht => ?_⟩
  obtain ⟨⟨h1, h2, h3, h4, ⟨hT0, hTmono⟩, hcap⟩, hni⟩ := hsol
  have hF : ∀ t, 0 ≤ t → ∀ i, Fh t i = Th t i / ![m1, m2, m3, m4, m5] i := by
    intro t ht i
    have := h4 t ht i
    rw [rl_m] at this
    have hmi : 0 < ![m1, m2, m3, m4, m5] i := by fin_cases i <;> simp [hm1, hm2, hm3, hm4, hm5]
    rw [eq_div_iff hmi.ne']; linarith
  have hZ : ∀ t, 0 ≤ t → Zh t = ![Zh 0 0 + lam1 * t - Th t 0 / m1, Zh 0 1 + Th t 0 / m1 - Th t 1 / m2,
      Zh 0 2 + Th t 1 / m2 - Th t 2 / m3, Zh 0 3 + Th t 2 / m3 - Th t 3 / m4,
      Zh 0 4 + Th t 3 / m4 - Th t 4 / m5] := by
    intro t ht
    funext i
    rw [h1 t ht i, h3 t ht i, rl_route_sum, rl_lam]
    simp only [hF t ht]
    fin_cases i <;> simp <;> ring
  have hZ0 : ∀ i, 0 ≤ Zh 0 i := h2 0 le_rfl
  -- the two linear pieces, written in terms of `Th`
  set V1 : ℝ → ℝ := fun s => x1 * (Zh 0 0 + lam1 * s - Th s 0 / m1)
    + x3 * (Zh 0 0 + Zh 0 1 + Zh 0 2 + lam1 * s - Th s 2 / m3)
    + x5 * (Zh 0 0 + Zh 0 1 + Zh 0 2 + Zh 0 3 + Zh 0 4 + lam1 * s - Th s 4 / m5) with hV1
  set V2 : ℝ → ℝ := fun s => x2 * (Zh 0 0 + Zh 0 1 + lam1 * s - Th s 1 / m2)
    + x4 * (Zh 0 0 + Zh 0 1 + Zh 0 2 + Zh 0 3 + lam1 * s - Th s 3 / m4) with hV2
  have hV1eq : ∀ s, 0 ≤ s → V1 s = x1 * Zh s 0 + x3 * (Zh s 0 + Zh s 1 + Zh s 2)
      + x5 * (Zh s 0 + Zh s 1 + Zh s 2 + Zh s 3 + Zh s 4) := by
    intro s hs; rw [hZ s hs]; simp [hV1]; ring
  have hV2eq : ∀ s, 0 ≤ s → V2 s = x2 * (Zh s 0 + Zh s 1)
      + x4 * (Zh s 0 + Zh s 1 + Zh s 2 + Zh s 3) := by
    intro s hs; rw [hZ s hs]; simp [hV2]; ring
  have hTmon : ∀ j, Monotone (fun s => Th s j) := fun j x y h => hTmono h j
  have hTinc : ∀ s r, 0 ≤ s → s ≤ r → ∀ j, Th r j - Th s j ≤ r - s := by
    intro s r hs hsr j
    have hc0 := hcap s r hs hsr 0
    have hc1 := hcap s r hs hsr 1
    rw [rl_pool_sum, rl_b] at hc0 hc1
    simp at hc0 hc1
    have := hTmono hsr
    fin_cases j <;> simp <;> linarith [this 0, this 1, this 2, this 3, this 4]
  have hTc : ∀ j, ContinuousOn (fun s => Th s j) (Ici 0) := by
    intro j
    refine (LipschitzOnWith.of_dist_le_mul (K := 1) fun x hx y hy => ?_).continuousOn
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    rcases le_total x y with hxy | hxy
    · have := hTinc x y hx hxy j
      have := hTmon j hxy
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · have := hTinc y x hy hxy j
      have := hTmon j hxy
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
  have hV1c : ContinuousOn V1 (Ioi 0) := by
    have := fun j => (hTc j).mono (Ioi_subset_Ici_self (a := (0:ℝ)))
    simp only [hV1]
    fun_prop
  have hV2c : ContinuousOn V2 (Ioi 0) := by
    have := fun j => (hTc j).mono (Ioi_subset_Ici_self (a := (0:ℝ)))
    simp only [hV2]
    fun_prop
  have hV1up : ∀ s h, 0 ≤ s → 0 ≤ h → V1 (s + h) ≤ V1 s + M * h := by
    intro s h hs hh
    have a0 := hTmon 0 (show s ≤ s + h by linarith)
    have a2 := hTmon 2 (show s ≤ s + h by linarith)
    have a4 := hTmon 4 (show s ≤ s + h by linarith)
    simp only at a0 a2 a4
    have k1 := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right a0 hm1.le) hx1.le
    have k3 := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right a2 hm3.le) hx3.le
    have k5 := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right a4 hm5.le) hx5.le
    have k0 : 0 ≤ lam1 * S2 * h := by positivity
    simp only [hV1, hM]
    linarith
  have hV2up : ∀ s h, 0 ≤ s → 0 ≤ h → V2 (s + h) ≤ V2 s + M * h := by
    intro s h hs hh
    have a1 := hTmon 1 (show s ≤ s + h by linarith)
    have a3 := hTmon 3 (show s ≤ s + h by linarith)
    simp only at a1 a3
    have k2 := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right a1 hm2.le) hx2.le
    have k4 := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right a3 hm4.le) hx4.le
    have k0 : 0 ≤ lam1 * S1 * h := by positivity
    simp only [hV2, hM]
    linarith
  set f : ℝ → ℝ := fun s => max (V1 s) (V2 s) with hf
  have hle1 : ∀ s, V1 s ≤ f s := fun s => le_max_left _ _
  have hle2 : ∀ s, V2 s ≤ f s := fun s => le_max_right _ _
  have hV1nn : ∀ s, 0 ≤ s → 0 ≤ V1 s := by
    intro s hs; rw [hV1eq s hs]
    have hZs := h2 s hs
    have := hZs 0; have := hZs 1; have := hZs 2; have := hZs 3; have := hZs 4
    positivity
  have hfnn : ∀ s, 0 ≤ s → 0 ≤ f s := fun s hs => le_trans (hV1nn s hs) (hle1 s)
  have hfc : ContinuousOn f (Ioi 0) := continuous_max.comp_continuousOn (hV1c.prodMk hV2c)
  have hfup : ∀ s h, 0 ≤ s → 0 ≤ h → f (s + h) ≤ f s + M * h := by
    intro s h hs hh
    refine max_le ?_ ?_
    · linarith [hV1up s h hs hh, hle1 s]
    · linarith [hV2up s h hs hh, hle2 s]
  have hbound : ∀ a b : ℝ, 0 ≤ a → a < b →
      ∃ M' : ℝ, 0 < M' ∧ ∀ t ∈ Ico a b, rgDini f t ≤ (M' : EReal) := by
    intro a' b' ha' _
    refine ⟨M, hMpos, fun s hs => rg_dini_le f s M ?_⟩
    filter_upwards [self_mem_nhdsWithin] with h hh
    have := hfup s h (ha'.trans hs.1) (le_of_lt hh)
    linarith
  -- non-idling, pool by pool
  have hni0 : ∀ t, 0 < t → 0 < Zh t 0 + Zh t 2 + Zh t 4 → ∀ d,
      HasDerivAt (fun s => Th s 0 + Th s 2 + Th s 4) d t → d = 1 := by
    intro t ht hpos d hd
    have := hni 0 t ht
    simp only [rl_pool_sum, rl_b] at this
    simp at this
    exact this hpos d hd
  have hni1 : ∀ t, 0 < t → 0 < Zh t 1 + Zh t 3 → ∀ d,
      HasDerivAt (fun s => Th s 1 + Th s 3) d t → d = 1 := by
    intro t ht hpos d hd
    have := hni 1 t ht
    simp only [rl_pool_sum, rl_b] at this
    simp at this
    exact this hpos d hd
  -- drift
  have hdrift : ∀ᵐ s, 0 ≤ s → 0 < f s → rgDini f s ≤ ((-(ε / 2) : ℝ) : EReal) := by
    have hdiff : ∀ᵐ s, ∀ j, DifferentiableAt ℝ (fun s => Th s j) s :=
      ae_all_iff.mpr fun j => (hTmon j).ae_differentiableAt
    filter_upwards [hdiff, compl_mem_ae_iff.mpr (measure_singleton (0:ℝ))] with s hs hs0 hsnn hfpos
    have hspos : 0 < s := lt_of_le_of_ne hsnn (Ne.symm hs0)
    set τ : Fin 5 → ℝ := fun j => deriv (fun s => Th s j) s with hτdef
    have hτ : ∀ j, HasDerivAt (fun s => Th s j) (τ j) s := fun j => (hs j).hasDerivAt
    have hτnn : ∀ j, 0 ≤ τ j := fun j => rl_deriv_nonneg_of_mono _ (hTmon j) _ _ (hτ j)
    set d1 := lam1 * S1 - (x1 * τ 0 / m1 + x3 * τ 2 / m3 + x5 * τ 4 / m5) with hd1
    set d2 := lam1 * S2 - (x2 * τ 1 / m2 + x4 * τ 3 / m4) with hd2
    have hdV1 : HasDerivAt V1 d1 s := by
      have e := ((((hasDerivAt_id s).const_mul lam1).const_add (Zh 0 0)).sub ((hτ 0).div_const m1)).const_mul x1
        |>.add (((((hasDerivAt_id s).const_mul lam1).const_add (Zh 0 0 + Zh 0 1 + Zh 0 2)).sub
          ((hτ 2).div_const m3)).const_mul x3)
        |>.add (((((hasDerivAt_id s).const_mul lam1).const_add (Zh 0 0 + Zh 0 1 + Zh 0 2 + Zh 0 3 + Zh 0 4)).sub
          ((hτ 4).div_const m5)).const_mul x5)
      refine e.congr_deriv ?_
      simp only [hd1, hS1]; ring
    have hdV2 : HasDerivAt V2 d2 s := by
      have e := ((((hasDerivAt_id s).const_mul lam1).const_add (Zh 0 0 + Zh 0 1)).sub ((hτ 1).div_const m2)).const_mul x2
        |>.add (((((hasDerivAt_id s).const_mul lam1).const_add (Zh 0 0 + Zh 0 1 + Zh 0 2 + Zh 0 3)).sub
          ((hτ 3).div_const m4)).const_mul x4)
      refine e.congr_deriv ?_
      simp only [hd2, hS2]; ring
    have hZs := h2 s hsnn
    have hZ0s := hZs 0; have hZ1s := hZs 1; have hZ2s := hZs 2; have hZ3s := hZs 3; have hZ4s := hZs 4
    have hG1 := hV1eq s hsnn
    have hG2 := hV2eq s hsnn
    have key1 : V1 s = f s → d1 ≤ -ε := by
      intro hVf
      rcases lt_or_ge 0 (Zh s 0 + Zh s 2 + Zh s 4) with hpos | hzero
      · have hsum := hni0 s hspos hpos _ (((hτ 0).add (hτ 2)).add (hτ 4))
        have := mul_le_mul_of_nonneg_right e1 (hτnn 0)
        have := mul_le_mul_of_nonneg_right e3 (hτnn 2)
        have := mul_le_mul_of_nonneg_right e5 (hτnn 4)
        simp only [hd1]
        have q1 : x1 * τ 0 / m1 = x1 / m1 * τ 0 := by ring
        have q3 : x3 * τ 2 / m3 = x3 / m3 * τ 2 := by ring
        have q5 : x5 * τ 4 / m5 = x5 / m5 * τ 4 := by ring
        rw [q1, q3, q5]
        have hs' : (lam1 * S1 + ε) * (τ 0 + τ 2 + τ 4) = lam1 * S1 + ε := by rw [hsum, mul_one]
        linarith
      · exfalso
        have z0 : Zh s 0 = 0 := by linarith
        have z2 : Zh s 2 = 0 := by linarith
        have z4 : Zh s 4 = 0 := by linarith
        rw [z0, z2, z4] at hG1
        rw [z0, z2] at hG2
        have hpos24 : 0 < Zh s 1 + Zh s 3 := by
          by_contra hcon
          push Not at hcon
          have y1 : Zh s 1 = 0 := by linarith
          have y3 : Zh s 3 = 0 := by linarith
          rw [hVf, y1, y3] at hG1
          linarith
        have : V1 s < V2 s := by
          rw [hG1, hG2]
          set c := min (x2 + x4 - x3 - x5) (x4 - x5) with hc
          have hcpos : 0 < c := lt_min (by linarith) (by linarith)
          have k1 := mul_le_mul_of_nonneg_right (min_le_left (x2 + x4 - x3 - x5) (x4 - x5)) hZ1s
          have k3 := mul_le_mul_of_nonneg_right (min_le_right (x2 + x4 - x3 - x5) (x4 - x5)) hZ3s
          have k := mul_pos hcpos hpos24
          rw [← hc] at k1 k3
          linarith
        linarith [hle2 s]
    have key2 : V2 s = f s → d2 ≤ -ε := by
      intro hVf
      rcases lt_or_ge 0 (Zh s 1 + Zh s 3) with hpos | hzero
      · have hsum := hni1 s hspos hpos _ ((hτ 1).add (hτ 3))
        have := mul_le_mul_of_nonneg_right e2 (hτnn 1)
        have := mul_le_mul_of_nonneg_right e4 (hτnn 3)
        simp only [hd2]
        have q2 : x2 * τ 1 / m2 = x2 / m2 * τ 1 := by ring
        have q4 : x4 * τ 3 / m4 = x4 / m4 * τ 3 := by ring
        rw [q2, q4]
        have hs' : (lam1 * S2 + ε) * (τ 1 + τ 3) = lam1 * S2 + ε := by rw [hsum, mul_one]
        linarith
      · exfalso
        have z1 : Zh s 1 = 0 := by linarith
        have z3 : Zh s 3 = 0 := by linarith
        rw [z1, z3] at hG1 hG2
        have hpos135 : 0 < Zh s 0 + Zh s 2 + Zh s 4 := by
          by_contra hcon
          push Not at hcon
          have y0 : Zh s 0 = 0 := by linarith
          have y2 : Zh s 2 = 0 := by linarith
          have y4 : Zh s 4 = 0 := by linarith
          rw [hVf, y0, y2] at hG2
          linarith
        have : V2 s < V1 s := by
          rw [hG1, hG2]
          set c := min (min (x1 + x3 + x5 - x2 - x4) (x3 + x5 - x4)) x5 with hc
          have hcpos : 0 < c := lt_min (lt_min (by linarith) (by linarith)) hx5
          have c0 : c ≤ x1 + x3 + x5 - x2 - x4 := le_trans (min_le_left _ _) (min_le_left _ _)
          have c2 : c ≤ x3 + x5 - x4 := le_trans (min_le_left _ _) (min_le_right _ _)
          have c4 : c ≤ x5 := min_le_right _ _
          have k0 := mul_le_mul_of_nonneg_right c0 hZ0s
          have k2 := mul_le_mul_of_nonneg_right c2 hZ2s
          have k4 := mul_le_mul_of_nonneg_right c4 hZ4s
          have k := mul_pos hcpos hpos135
          linarith
        linarith [hle1 s]
    refine rg_dini_le f s _ ?_
    have hall1 : ∀ᶠ h in 𝓝[>] (0:ℝ), V1 (s + h) ≤ f s - ε / 2 * h := by
      by_cases hkF : V1 s = f s
      · have hdk := key1 hkF
        have ht := hdV1.tendsto_slope_zero_right
        filter_upwards [ht.eventually (gt_mem_nhds (show d1 < -(ε / 2) by linarith)),
          self_mem_nhdsWithin] with h hh hh0
        have hh0' : (0:ℝ) < h := hh0
        rw [smul_eq_mul, inv_mul_lt_iff₀ hh0'] at hh
        linarith
      · have hlt : V1 s < f s := lt_of_le_of_ne (hle1 s) hkF
        have hδ : 0 < (f s - V1 s) / (M + ε / 2) := div_pos (by linarith) (by linarith)
        filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
        have hh1 : 0 < h := hh.1
        have hh2 : h < (f s - V1 s) / (M + ε / 2) := hh.2
        have := hV1up s h hsnn hh1.le
        rw [lt_div_iff₀ (by linarith)] at hh2
        linarith
    have hall2 : ∀ᶠ h in 𝓝[>] (0:ℝ), V2 (s + h) ≤ f s - ε / 2 * h := by
      by_cases hkF : V2 s = f s
      · have hdk := key2 hkF
        have ht := hdV2.tendsto_slope_zero_right
        filter_upwards [ht.eventually (gt_mem_nhds (show d2 < -(ε / 2) by linarith)),
          self_mem_nhdsWithin] with h hh hh0
        have hh0' : (0:ℝ) < h := hh0
        rw [smul_eq_mul, inv_mul_lt_iff₀ hh0'] at hh
        linarith
      · have hlt : V2 s < f s := lt_of_le_of_ne (hle2 s) hkF
        have hδ : 0 < (f s - V2 s) / (M + ε / 2) := div_pos (by linarith) (by linarith)
        filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
        have hh1 : 0 < h := hh.1
        have hh2 : h < (f s - V2 s) / (M + ε / 2) := hh.2
        have := hV2up s h hsnn hh1.le
        rw [lt_div_iff₀ (by linarith)] at hh2
        linarith
    filter_upwards [hall1, hall2] with h hh1 hh2
    have : f (s + h) ≤ f s - ε / 2 * h := max_le hh1 hh2
    linarith
  have hext := rgd_extinction f hfnn hfc hbound (ε / 2) (by positivity) hdrift
  have hf0 : f 0 ≤ (S1 + S2) * ∑ i, Zh 0 i := by
    rw [Fin.sum_univ_five]
    have z0 := hZ0 0; have z1 := hZ0 1; have z2 := hZ0 2; have z3 := hZ0 3; have z4 := hZ0 4
    set tot := Zh 0 0 + Zh 0 1 + Zh 0 2 + Zh 0 3 + Zh 0 4 with htot
    have k1 := mul_le_mul_of_nonneg_left (show Zh 0 0 ≤ tot by linarith) hx1.le
    have k3 := mul_le_mul_of_nonneg_left (show Zh 0 0 + Zh 0 1 + Zh 0 2 ≤ tot by linarith) hx3.le
    have k2 := mul_le_mul_of_nonneg_left (show Zh 0 0 + Zh 0 1 ≤ tot by linarith) hx2.le
    have k4 := mul_le_mul_of_nonneg_left (show Zh 0 0 + Zh 0 1 + Zh 0 2 + Zh 0 3 ≤ tot by linarith) hx4.le
    have kS1 : 0 ≤ S1 * tot := mul_nonneg hS1pos.le (by linarith)
    have kS2 : 0 ≤ S2 * tot := mul_nonneg hS2pos.le (by linarith)
    refine max_le ?_ ?_
    · rw [hV1eq 0 le_rfl]; linarith
    · rw [hV2eq 0 le_rfl]; linarith
  have htf : f 0 / (ε / 2) ≤ t := by
    rw [div_le_iff₀ (by positivity)]
    have hsum : 0 ≤ ∑ i, Zh 0 i := Finset.sum_nonneg fun i _ => hZ0 i
    have : 2 * (S1 + S2) / ε * (∑ i, Zh 0 i) * (ε / 2) = (S1 + S2) * ∑ i, Zh 0 i := by
      field_simp
    have h' := mul_le_mul_of_nonneg_right ht (show 0 ≤ ε / 2 by positivity)
    linarith
  have hft := hext t htf
  have ht0 : 0 ≤ t := le_trans (div_nonneg (hfnn 0 le_rfl) (by positivity)) htf
  have hV1t : V1 t = 0 := le_antisymm (hft ▸ hle1 t) (hV1nn t ht0)
  rw [hV1eq t ht0] at hV1t
  have hZt := h2 t ht0
  have w0 := hZt 0; have w1 := hZt 1; have w2 := hZt 2; have w3 := hZt 3; have w4 := hZt 4
  have k1 := mul_nonneg hx1.le w0
  have k3 := mul_nonneg hx3.le (show 0 ≤ Zh t 0 + Zh t 1 + Zh t 2 by linarith)
  have k5 := mul_nonneg hx5.le (show 0 ≤ Zh t 0 + Zh t 1 + Zh t 2 + Zh t 3 + Zh t 4 by linarith)
  have htot : x5 * (Zh t 0 + Zh t 1 + Zh t 2 + Zh t 3 + Zh t 4) = 0 := by linarith
  have htot' : Zh t 0 + Zh t 1 + Zh t 2 + Zh t 3 + Zh t 4 = 0 :=
    (mul_eq_zero.mp htot).resolve_left hx5.ne'
  funext j
  fin_cases j <;> simp <;> linarith

/-- Linear (constant-rate) fluid solutions of the re-entrant line. -/
theorem rl_linear_solution (lam1 m1 m2 m3 m4 m5 : ℝ)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm3 : 0 < m3) (hm4 : 0 < m4) (hm5 : 0 < m5)
    (τ : Fin 5 → ℝ) (hτ : ∀ i, 0 ≤ τ i) (hc1 : τ 0 + τ 2 + τ 4 ≤ 1) (hc2 : τ 1 + τ 3 ≤ 1)
    (Z0 : Fin 5 → ℝ) (hZ0 : ∀ i, 0 ≤ Z0 i) (v : Fin 5 → ℝ)
    (hv : v = ![lam1 - τ 0 / m1, τ 0 / m1 - τ 1 / m2, τ 1 / m2 - τ 2 / m3, τ 2 / m3 - τ 3 / m4,
      τ 3 / m4 - τ 4 / m5])
    (hvnn : ∀ i, 0 ≤ v i)
    (hni1 : τ 0 + τ 2 + τ 4 = 1 ∨ (Z0 0 + Z0 2 + Z0 4 = 0 ∧ v 0 + v 2 + v 4 = 0))
    (hni2 : τ 1 + τ 3 = 1 ∨ (Z0 1 + Z0 3 = 0 ∧ v 1 + v 3 = 0)) :
    IsNonIdlingSolution (reentrantLineData lam1 m1 m2 m3 m4 m5)
      (fun t i => τ i / ![m1, m2, m3, m4, m5] i * t) (fun t i => τ i / ![m1, m2, m3, m4, m5] i * t)
      (fun t i => τ i * t) (fun t i => Z0 i + v i * t) := by
  have hmpos : ∀ i, 0 < ![m1, m2, m3, m4, m5] i := by
    intro i; fin_cases i <;> simp [hm1, hm2, hm3, hm4, hm5]
  refine ⟨⟨?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro t ht i
    rw [rl_route_sum, rl_lam]
    fin_cases i <;> simp [hv] <;> ring
  · intro t ht i
    exact add_nonneg (hZ0 i) (mul_nonneg (hvnn i) ht)
  · intro t ht i; rfl
  · intro t ht i
    rw [rl_m]
    have := (hmpos i).ne'
    field_simp
  · funext i; simp
  · intro s t hst i
    simp only
    exact mul_le_mul_of_nonneg_left hst (hτ i)
  · intro s t hs hst k
    rw [rl_pool_sum, rl_b]
    fin_cases k <;> simp <;> nlinarith
  · intro k t ht hpos d hd
    rw [rl_pool_sum] at hpos
    rw [rl_b]
    have hd' : HasDerivAt (fun s => ∑ i ∈ poolBuffers (reentrantLineData lam1 m1 m2 m3 m4 m5) k, τ i * s)
        (∑ i ∈ poolBuffers (reentrantLineData lam1 m1 m2 m3 m4 m5) k, τ i) t := by
      have := (hasDerivAt_id t).const_mul (∑ i ∈ poolBuffers (reentrantLineData lam1 m1 m2 m3 m4 m5) k, τ i)
      refine this.congr_deriv (by simp) |>.congr_of_eventuallyEq ?_
      filter_upwards with s
      simp [Finset.sum_mul]
    have hdeq := hd.unique hd'
    rw [rl_pool_sum] at hdeq
    fin_cases k
    · simp at hpos hdeq ⊢
      rcases hni1 with h | ⟨h1, h2⟩
      · linarith
      · exfalso
        have := hZ0 0; have := hZ0 2; have := hZ0 4
        have := hvnn 0; have := hvnn 2; have := hvnn 4
        nlinarith
    · simp at hpos hdeq ⊢
      rcases hni2 with h | ⟨h1, h2⟩
      · linarith
      · exfalso
        have := hZ0 1; have := hZ0 3
        have := hvnn 1; have := hvnn 3
        nlinarith


theorem rl_not_stable_of_linear (lam1 m1 m2 m3 m4 m5 : ℝ)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm3 : 0 < m3) (hm4 : 0 < m4) (hm5 : 0 < m5)
    (τ : Fin 5 → ℝ) (hτ : ∀ i, 0 ≤ τ i) (hc1 : τ 0 + τ 2 + τ 4 ≤ 1) (hc2 : τ 1 + τ 3 ≤ 1)
    (Z0 : Fin 5 → ℝ) (hZ0 : ∀ i, 0 ≤ Z0 i) (v : Fin 5 → ℝ)
    (hv : v = ![lam1 - τ 0 / m1, τ 0 / m1 - τ 1 / m2, τ 1 / m2 - τ 2 / m3, τ 2 / m3 - τ 3 / m4,
      τ 3 / m4 - τ 4 / m5])
    (hvnn : ∀ i, 0 ≤ v i)
    (hni1 : τ 0 + τ 2 + τ 4 = 1 ∨ (Z0 0 + Z0 2 + Z0 4 = 0 ∧ v 0 + v 2 + v 4 = 0))
    (hni2 : τ 1 + τ 3 = 1 ∨ (Z0 1 + Z0 3 = 0 ∧ v 1 + v 3 = 0))
    (hpos : ∃ i, 0 < Z0 i) :
    ¬ FluidModelGloballyStable (reentrantLineData lam1 m1 m2 m3 m4 m5) := by
  rintro ⟨γ, hγ, hall⟩
  obtain ⟨i0, hi0⟩ := hpos
  have hsol := rl_linear_solution lam1 m1 m2 m3 m4 m5 hm1 hm2 hm3 hm4 hm5 τ hτ hc1 hc2 Z0 hZ0 v hv
    hvnn hni1 hni2
  have h := hall _ _ _ _ hsol (γ * ∑ i, (Z0 i + v i * 0)) le_rfl
  have ht : 0 ≤ γ * ∑ i, (Z0 i + v i * 0) :=
    mul_nonneg hγ.le (Finset.sum_nonneg fun i _ => by simpa using hZ0 i)
  have h2 : Z0 i0 + v i0 * (γ * ∑ i, (Z0 i + v i * 0)) = 0 := congrFun h i0
  have := mul_nonneg (hvnn i0) ht
  linarith

theorem rl_unstable_load (lam1 m1 m2 m3 m4 m5 : ℝ) (hlam1 : 0 < lam1)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm3 : 0 < m3) (hm4 : 0 < m4) (hm5 : 0 < m5)
    (h : 1 ≤ lam1 * (m1 + m3 + m5) ∨ 1 ≤ lam1 * (m2 + m4)) :
    ¬ FluidModelGloballyStable (reentrantLineData lam1 m1 m2 m3 m4 m5) := by
  have hS1 : 0 < m1 + m3 + m5 := by linarith
  have hS2 : 0 < m2 + m4 := by linarith
  by_cases hcase : 1 ≤ lam1 * (m1 + m3 + m5) ∧ m2 + m4 ≤ m1 + m3 + m5
  · -- station 1 is the bottleneck
    obtain ⟨h1, h2⟩ := hcase
    set θ := 1 / (m1 + m3 + m5) with hθ
    have hθpos : 0 < θ := by positivity
    have hθ1 : θ * (m1 + m3 + m5) = 1 := by rw [hθ]; field_simp
    have hθl : θ ≤ lam1 := by
      rw [hθ, div_le_iff₀ hS1]; linarith
    refine rl_not_stable_of_linear lam1 m1 m2 m3 m4 m5 hm1 hm2 hm3 hm4 hm5
      ![m1 * θ, m2 * θ, m3 * θ, m4 * θ, m5 * θ] ?_ ?_ ?_ ![1, 0, 0, 0, 0] ?_
      ![lam1 - θ, 0, 0, 0, 0] ?_ ?_ ?_ ?_ ⟨0, by simp⟩
    · intro i; fin_cases i <;> simp <;> positivity
    · simp; linarith
    · simp; nlinarith
    · intro i; fin_cases i <;> simp
    · have h1' : m1 * θ / m1 = θ := by field_simp
      have h2' : m2 * θ / m2 = θ := by field_simp
      have h3' : m3 * θ / m3 = θ := by field_simp
      have h4' : m4 * θ / m4 = θ := by field_simp
      have h5' : m5 * θ / m5 = θ := by field_simp
      simp [h1', h2', h3', h4', h5']
    · intro i; fin_cases i <;> simp <;> linarith
    · left; simp; linarith
    · right; simp
  · have hcase' : 1 ≤ lam1 * (m2 + m4) ∧ m1 + m3 + m5 ≤ m2 + m4 := by
      rcases h with h | h
      · have : ¬ (m2 + m4 ≤ m1 + m3 + m5) := fun h' => hcase ⟨h, h'⟩
        push Not at this
        exact ⟨by nlinarith, this.le⟩
      · by_cases h' : m1 + m3 + m5 ≤ m2 + m4
        · exact ⟨h, h'⟩
        · push Not at h'
          exact absurd ⟨by nlinarith, h'.le⟩ hcase
    obtain ⟨h1, h2⟩ := hcase'
    set θ := 1 / (m2 + m4) with hθ
    have hθpos : 0 < θ := by positivity
    have hθ1 : θ * (m2 + m4) = 1 := by rw [hθ]; field_simp
    have hθl : θ ≤ lam1 := by
      rw [hθ, div_le_iff₀ hS2]; linarith
    have hθS : θ * (m1 + m3 + m5) ≤ 1 := by
      rw [hθ, div_mul_eq_mul_div, div_le_iff₀ hS2]; linarith
    have h2' : m2 * θ / m2 = θ := by field_simp
    have h3' : m3 * θ / m3 = θ := by field_simp
    have h4' : m4 * θ / m4 = θ := by field_simp
    have h5' : m5 * θ / m5 = θ := by field_simp
    by_cases hsub : lam1 * m1 + θ * (m3 + m5) ≤ 1
    · -- station 1 can keep up; mass in class 2
      refine rl_not_stable_of_linear lam1 m1 m2 m3 m4 m5 hm1 hm2 hm3 hm4 hm5
        ![lam1 * m1, m2 * θ, m3 * θ, m4 * θ, m5 * θ] ?_ ?_ ?_ ![0, 1, 0, 0, 0] ?_
        ![0, lam1 - θ, 0, 0, 0] ?_ ?_ ?_ ?_ ⟨1, by simp⟩
      · intro i; fin_cases i <;> simp <;> positivity
      · simp; linarith
      · simp; linarith
      · intro i; fin_cases i <;> simp
      · have h1' : lam1 * m1 / m1 = lam1 := by field_simp
        simp [h1', h2', h3', h4', h5']
      · intro i; fin_cases i <;> simp <;> linarith
      · right; simp
      · left; simp; linarith
    · push Not at hsub
      set τ0 := 1 - θ * (m3 + m5) with hτ0
      have hτ0nn : 0 ≤ τ0 := by rw [hτ0]; nlinarith
      have hτ0lt : τ0 < lam1 * m1 := by rw [hτ0]; linarith
      have hτ0ge : m1 * θ ≤ τ0 := by rw [hτ0]; nlinarith
      refine rl_not_stable_of_linear lam1 m1 m2 m3 m4 m5 hm1 hm2 hm3 hm4 hm5
        ![τ0, m2 * θ, m3 * θ, m4 * θ, m5 * θ] ?_ ?_ ?_ ![1, 0, 0, 0, 0] ?_
        ![lam1 - τ0 / m1, τ0 / m1 - θ, 0, 0, 0] ?_ ?_ ?_ ?_ ⟨0, by simp⟩
      · intro i; fin_cases i <;> simp <;> positivity
      · simp; rw [hτ0]; ring_nf; rfl
      · simp; linarith
      · intro i; fin_cases i <;> simp
      · simp [h2', h3', h4', h5']
      · intro i; fin_cases i <;> simp
        · rw [div_le_iff₀ hm1]; linarith
        · rw [le_div_iff₀ hm1]; linarith
      · left; simp; rw [hτ0]; ring
      · left; simp; linarith

/-- The virtual-station case when the "linear" regime applies: `lam1 * m1 * m2 ≥ m2 - m3`. -/
theorem rl_unstable_vs_linear (lam1 m1 m2 m3 m4 m5 : ℝ) (hlam1 : 0 < lam1)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm3 : 0 < m3) (hm4 : 0 < m4) (hm5 : 0 < m5)
    (hc1 : lam1 * (m1 + m3 + m5) < 1) (hc2 : lam1 * (m2 + m4) < 1)
    (hvs : 1 ≤ lam1 * (m2 + m5)) (hlin : m2 - m3 ≤ lam1 * m1 * m2) :
    ¬ FluidModelGloballyStable (reentrantLineData lam1 m1 m2 m3 m4 m5) := by
  have hm2big : m1 + m3 < m2 := by nlinarith
  refine rl_not_stable_of_linear lam1 m1 m2 m3 m4 m5 hm1 hm2 hm3 hm4 hm5
    ![1 - m3 / m2, 1, m3 / m2, 0, 0] ?_ ?_ ?_ ![1, 0, 0, 0, 0] ?_
    ![lam1 - (1 - m3 / m2) / m1, (1 - m3 / m2) / m1 - 1 / m2, 0, 1 / m2, 0] ?_ ?_ ?_ ?_
    ⟨0, by simp⟩
  · have : m3 / m2 ≤ 1 := by rw [div_le_iff₀ hm2]; linarith
    intro i; fin_cases i <;> simp <;> linarith [div_nonneg hm3.le hm2.le]
  · simp
  · simp
  · intro i; fin_cases i <;> simp
  · ext i; fin_cases i <;> simp <;> field_simp <;> ring
  · have hφ : 1 - m3 / m2 = (m2 - m3) / m2 := by field_simp
    intro i; fin_cases i
    · show 0 ≤ lam1 - (1 - m3 / m2) / m1
      rw [hφ, div_div, sub_nonneg, div_le_iff₀ (by positivity)]; nlinarith
    · show 0 ≤ (1 - m3 / m2) / m1 - 1 / m2
      rw [hφ, div_div, sub_nonneg, div_le_div_iff₀ hm2 (by positivity)]; nlinarith
    · show (0:ℝ) ≤ 0; exact le_rfl
    · show 0 ≤ 1 / m2; positivity
    · show (0:ℝ) ≤ 0; exact le_rfl
  · left; simp
  · left; simp

/-- clamp `x` to `[0, w]`. -/
noncomputable def clampTo (x w : ℝ) : ℝ := min (max x 0) w

theorem clampTo_nonneg (x w : ℝ) (hw : 0 ≤ w) : 0 ≤ clampTo x w := by
  unfold clampTo; exact le_min (le_max_right _ _) hw
theorem clampTo_le (x w : ℝ) : clampTo x w ≤ w := min_le_right _ _
theorem clampTo_of_nonpos (x w : ℝ) (hx : x ≤ 0) (hw : 0 ≤ w) : clampTo x w = 0 := by
  unfold clampTo; rw [max_eq_right hx, min_eq_left hw]
theorem clampTo_of_ge (x w : ℝ) (hx : w ≤ x) (hw : 0 ≤ w) : clampTo x w = w := by
  unfold clampTo; rw [max_eq_left (hw.trans hx), min_eq_right hx]
theorem clampTo_of_mem (x w : ℝ) (h0 : 0 ≤ x) (hw : x ≤ w) : clampTo x w = x := by
  unfold clampTo; rw [max_eq_left h0, min_eq_left hw]
theorem clampTo_mono (x y w : ℝ) (hxy : x ≤ y) : clampTo x w ≤ clampTo y w := by
  unfold clampTo; exact min_le_min_right _ (max_le_max_right _ hxy)
theorem clampTo_glue (x w1 w2 : ℝ) (h1 : 0 ≤ w1) (h2 : 0 ≤ w2) :
    clampTo x w1 + clampTo (x - w1) w2 = clampTo x (w1 + w2) := by
  unfold clampTo
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem clampTo_lip (x y w : ℝ) (hxy : x ≤ y) : clampTo y w - clampTo x w ≤ y - x := by
  unfold clampTo
  simp only [max_def, min_def]
  split_ifs <;> linarith



/-- Parameters of the re-entrant line. -/
structure RLP where
  lam1 : ℝ
  m1 : ℝ
  m2 : ℝ
  m3 : ℝ
  m4 : ℝ
  m5 : ℝ

namespace RLP

noncomputable def dat (p : RLP) := reentrantLineData p.lam1 p.m1 p.m2 p.m3 p.m4 p.m5
noncomputable def phi (p : RLP) : ℝ := (p.m2 - p.m3) / (p.m1 * p.m2)
noncomputable def a (p : RLP) : ℝ := 1 / (p.phi - p.lam1)
noncomputable def z2 (p : RLP) : ℝ := (p.phi - 1 / p.m2) * p.a
noncomputable def b (p : RLP) : ℝ := p.z2 / (1 / p.m2 - p.lam1)
noncomputable def z4 (p : RLP) : ℝ := 1 / (1 - p.lam1 * p.m2)
noncomputable def c (p : RLP) : ℝ := p.m4 * p.z4
noncomputable def d (p : RLP) : ℝ := (p.m5 - p.m4) * p.z4
noncomputable def L (p : RLP) : ℝ := p.a + p.b + p.c + p.d
noncomputable def r (p : RLP) : ℝ := p.lam1 * p.m5 * p.z4
noncomputable def tA (p : RLP) : Fin 5 → ℝ := ![1 - p.m3 / p.m2, 1, p.m3 / p.m2, 0, 0]
noncomputable def tB (p : RLP) : Fin 5 → ℝ := ![p.lam1 * p.m1, 1, p.m3 / p.m2, 0, 0]
noncomputable def tC (p : RLP) : Fin 5 → ℝ := ![0, 0, 0, 1, 1]
noncomputable def tD (p : RLP) : Fin 5 → ℝ := ![0, 0, 0, 0, 1]
noncomputable def mv (p : RLP) : Fin 5 → ℝ := ![p.m1, p.m2, p.m3, p.m4, p.m5]

/-- unit-cycle cumulative service. -/
noncomputable def U (p : RLP) (σ : ℝ) (i : Fin 5) : ℝ :=
  p.tA i * clampTo σ p.a + p.tB i * clampTo (σ - p.a) p.b + p.tC i * clampTo (σ - p.a - p.b) p.c
    + p.tD i * clampTo (σ - p.a - p.b - p.c) p.d

structure Good (p : RLP) : Prop where
  hlam : 0 < p.lam1
  hm1 : 0 < p.m1
  hm2 : 0 < p.m2
  hm3 : 0 < p.m3
  hm4 : 0 < p.m4
  hm5 : 0 < p.m5
  hc1 : p.lam1 * (p.m1 + p.m3 + p.m5) < 1
  hc2 : p.lam1 * (p.m2 + p.m4) < 1
  hvs : 1 ≤ p.lam1 * (p.m2 + p.m5)
  hlt : p.lam1 * p.m1 * p.m2 < p.m2 - p.m3

variable {p : RLP} (hp : p.Good)
include hp

theorem m2_big : p.m1 + p.m3 < p.m2 := by nlinarith [hp.hvs, hp.hc1, hp.hlam]
theorem m5_big : p.m4 < p.m5 := by nlinarith [hp.hvs, hp.hc2, hp.hlam]
theorem lm2_lt : p.lam1 * p.m2 < 1 := by nlinarith [hp.hc2, hp.hlam, hp.hm4]
theorem phi_gt : p.lam1 < p.phi := by
  unfold phi; rw [lt_div_iff₀ (by nlinarith [hp.hm1, hp.hm2])]; linarith [hp.hlt]
theorem phi_ge : 1 / p.m2 ≤ p.phi := by
  unfold phi; rw [div_le_div_iff₀ hp.hm2 (by nlinarith [hp.hm1, hp.hm2])]
  nlinarith [m2_big hp, hp.hm2]
theorem a_pos : 0 < p.a := by unfold a; have := phi_gt hp; positivity
theorem z2_nonneg : 0 ≤ p.z2 := by
  unfold z2; exact mul_nonneg (by linarith [phi_ge hp]) (a_pos hp).le
theorem inv_m2_gt : p.lam1 < 1 / p.m2 := by
  rw [lt_div_iff₀ hp.hm2]; exact lm2_lt hp
theorem b_nonneg : 0 ≤ p.b := by
  unfold b; exact div_nonneg (z2_nonneg hp) (by linarith [inv_m2_gt hp])
theorem z4_pos : 0 < p.z4 := by unfold z4; have := lm2_lt hp; positivity
theorem c_pos : 0 < p.c := by unfold c; exact mul_pos hp.hm4 (z4_pos hp)
theorem d_pos : 0 < p.d := by unfold d; exact mul_pos (by linarith [m5_big hp]) (z4_pos hp)
theorem L_pos : 0 < p.L := by unfold L; linarith [a_pos hp, b_nonneg hp, c_pos hp, d_pos hp]
theorem r_ge : 1 ≤ p.r := by
  unfold r z4
  have := lm2_lt hp
  rw [mul_one_div, le_div_iff₀ (by linarith)]
  linarith [hp.hvs]
theorem a_eq : 1 + (p.lam1 - p.phi) * p.a = 0 := by
  have hne : p.phi - p.lam1 ≠ 0 := (sub_pos.mpr (phi_gt hp)).ne'
  unfold a; field_simp; ring
theorem b_eq : p.z2 + (p.lam1 - 1 / p.m2) * p.b = 0 := by
  have hne : 1 / p.m2 - p.lam1 ≠ 0 := (sub_pos.mpr (inv_m2_gt hp)).ne'
  unfold b; field_simp; ring
theorem ab_eq : (p.a + p.b) / p.m2 = p.z4 := by
  have h1 : p.phi - p.lam1 ≠ 0 := (sub_pos.mpr (phi_gt hp)).ne'
  have h2 : 1 / p.m2 - p.lam1 ≠ 0 := (sub_pos.mpr (inv_m2_gt hp)).ne'
  have h3 : 1 - p.lam1 * p.m2 ≠ 0 := (sub_pos.mpr (lm2_lt hp)).ne'
  have h4 := hp.hm2.ne'
  unfold z4 b z2 a
  field_simp
  ring
theorem c_eq : p.z4 - p.c / p.m4 = 0 := by
  unfold c; rw [mul_div_cancel_left₀ _ hp.hm4.ne', sub_self]
theorem d_eq : p.c * (1 / p.m4 - 1 / p.m5) - p.d / p.m5 = 0 := by
  unfold c d; have := hp.hm4; have := hp.hm5; field_simp; ring
omit hp in
theorem r_eq : p.lam1 * (p.c + p.d) = p.r := by
  unfold c d r; ring
theorem tA0 : p.tA 0 / p.m1 = p.phi := by
  unfold tA phi; simp; have := hp.hm1; have := hp.hm2; field_simp
theorem m3m2_le : p.m3 / p.m2 ≤ 1 := by
  rw [div_le_iff₀ hp.hm2]; linarith [m2_big hp, hp.hm1]
theorem tB_cap : p.lam1 * p.m1 + p.m3 / p.m2 ≤ 1 := by
  rw [← sub_nonneg]
  have hne := hp.hm2.ne'
  have : 1 - (p.lam1 * p.m1 + p.m3 / p.m2) = (p.m2 - p.m3 - p.lam1 * p.m1 * p.m2) / p.m2 := by
    field_simp; ring
  rw [this]; exact div_nonneg (by linarith [hp.hlt]) hp.hm2.le


/-- unit-cycle fluid state. -/
noncomputable def Y (p : RLP) (σ : ℝ) : Fin 5 → ℝ :=
  ![1 + p.lam1 * clampTo σ p.L - p.U σ 0 / p.m1, p.U σ 0 / p.m1 - p.U σ 1 / p.m2,
    p.U σ 1 / p.m2 - p.U σ 2 / p.m3, p.U σ 2 / p.m3 - p.U σ 3 / p.m4, p.U σ 3 / p.m4 - p.U σ 4 / p.m5]

noncomputable def ab (p : RLP) : ℝ := p.a + p.b
noncomputable def abc (p : RLP) : ℝ := p.a + p.b + p.c

theorem L_eq : p.L = p.abc + p.d := by unfold L abc; ring
theorem abc_eq : p.abc = p.ab + p.c := by unfold abc ab; ring

theorem U_A (σ : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ p.a) (i : Fin 5) : p.U σ i = p.tA i * σ := by
  unfold U
  rw [clampTo_of_mem _ _ h0 h1, clampTo_of_nonpos _ _ (by linarith) (b_nonneg hp),
    clampTo_of_nonpos _ _ (by linarith [b_nonneg hp]) (c_pos hp).le,
    clampTo_of_nonpos _ _ (by linarith [b_nonneg hp, c_pos hp]) (d_pos hp).le]
  ring

theorem U_B (σ : ℝ) (h0 : p.a ≤ σ) (h1 : σ ≤ p.ab) (i : Fin 5) :
    p.U σ i = p.tA i * p.a + p.tB i * (σ - p.a) := by
  unfold U; unfold ab at h1
  rw [clampTo_of_ge _ _ h0 (a_pos hp).le, clampTo_of_mem _ _ (by linarith) (by linarith),
    clampTo_of_nonpos _ _ (by linarith) (c_pos hp).le,
    clampTo_of_nonpos _ _ (by linarith [c_pos hp]) (d_pos hp).le]
  ring

theorem U_C (σ : ℝ) (h0 : p.ab ≤ σ) (h1 : σ ≤ p.abc) (i : Fin 5) :
    p.U σ i = p.tA i * p.a + p.tB i * p.b + p.tC i * (σ - p.a - p.b) := by
  unfold U; unfold ab at h0; unfold abc at h1
  rw [clampTo_of_ge _ _ (by linarith [b_nonneg hp]) (a_pos hp).le,
    clampTo_of_ge _ _ (by linarith) (b_nonneg hp),
    clampTo_of_mem _ _ (by linarith) (by linarith),
    clampTo_of_nonpos _ _ (by linarith) (d_pos hp).le]
  ring

theorem U_D (σ : ℝ) (h0 : p.abc ≤ σ) (h1 : σ ≤ p.L) (i : Fin 5) :
    p.U σ i = p.tA i * p.a + p.tB i * p.b + p.tC i * p.c + p.tD i * (σ - p.a - p.b - p.c) := by
  unfold U; unfold abc at h0; unfold L at h1
  rw [clampTo_of_ge _ _ (by linarith [b_nonneg hp, c_pos hp]) (a_pos hp).le,
    clampTo_of_ge _ _ (by linarith [c_pos hp]) (b_nonneg hp),
    clampTo_of_ge _ _ (by linarith) (c_pos hp).le,
    clampTo_of_mem _ _ (by linarith) (by linarith)]

theorem U_nonpos (σ : ℝ) (h : σ ≤ 0) (i : Fin 5) : p.U σ i = 0 := by
  unfold U
  rw [clampTo_of_nonpos _ _ h (a_pos hp).le, clampTo_of_nonpos _ _ (by linarith [a_pos hp]) (b_nonneg hp),
    clampTo_of_nonpos _ _ (by linarith [a_pos hp, b_nonneg hp]) (c_pos hp).le,
    clampTo_of_nonpos _ _ (by linarith [a_pos hp, b_nonneg hp, c_pos hp]) (d_pos hp).le]
  ring

theorem U_ge (σ : ℝ) (h : p.L ≤ σ) (i : Fin 5) : p.U σ i = p.U p.L i := by
  unfold U; unfold L at h ⊢
  rw [clampTo_of_ge _ _ (by linarith [b_nonneg hp, c_pos hp, d_pos hp]) (a_pos hp).le,
    clampTo_of_ge _ _ (by linarith [c_pos hp, d_pos hp]) (b_nonneg hp),
    clampTo_of_ge _ _ (by linarith [d_pos hp]) (c_pos hp).le,
    clampTo_of_ge _ _ (by linarith) (d_pos hp).le,
    clampTo_of_ge _ _ (by linarith [b_nonneg hp, c_pos hp, d_pos hp]) (a_pos hp).le,
    clampTo_of_ge _ _ (by linarith [c_pos hp, d_pos hp]) (b_nonneg hp),
    clampTo_of_ge _ _ (by linarith [d_pos hp]) (c_pos hp).le,
    clampTo_of_ge _ _ (by linarith) (d_pos hp).le]

theorem U_zero (i : Fin 5) : p.U 0 i = 0 := U_nonpos hp 0 le_rfl i

theorem U_mono (σ σ' : ℝ) (h : σ ≤ σ') (i : Fin 5) : p.U σ i ≤ p.U σ' i := by
  have hA : 0 ≤ p.tA i := by
    unfold tA; fin_cases i <;> simp <;> [linarith [m3m2_le hp]; exact div_nonneg hp.hm3.le hp.hm2.le]
  have hB : 0 ≤ p.tB i := by
    unfold tB; fin_cases i <;> simp <;> [exact mul_nonneg hp.hlam.le hp.hm1.le; exact div_nonneg hp.hm3.le hp.hm2.le]
  have hC : 0 ≤ p.tC i := by unfold tC; fin_cases i <;> simp
  have hD : 0 ≤ p.tD i := by unfold tD; fin_cases i <;> simp
  unfold U
  have := clampTo_mono σ σ' p.a h
  have := clampTo_mono (σ - p.a) (σ' - p.a) p.b (by linarith)
  have := clampTo_mono (σ - p.a - p.b) (σ' - p.a - p.b) p.c (by linarith)
  have := clampTo_mono (σ - p.a - p.b - p.c) (σ' - p.a - p.b - p.c) p.d (by linarith)
  gcongr

theorem clamp_tiling (σ : ℝ) :
    clampTo σ p.a + clampTo (σ - p.a) p.b + clampTo (σ - p.a - p.b) p.c
      + clampTo (σ - p.a - p.b - p.c) p.d = clampTo σ p.L := by
  have h1 := clampTo_glue σ p.a p.b (a_pos hp).le (b_nonneg hp)
  have h2 := clampTo_glue σ (p.a + p.b) p.c (by linarith [a_pos hp, b_nonneg hp]) (c_pos hp).le
  have h3 := clampTo_glue σ (p.a + p.b + p.c) p.d (by linarith [a_pos hp, b_nonneg hp, c_pos hp])
    (d_pos hp).le
  unfold L
  rw [show σ - p.a - p.b - p.c = σ - (p.a + p.b + p.c) by ring, show σ - p.a - p.b = σ - (p.a + p.b) by ring]
  linarith

theorem U_pool1 (σ : ℝ) : p.U σ 0 + p.U σ 2 + p.U σ 4 = clampTo σ p.a
    + (p.lam1 * p.m1 + p.m3 / p.m2) * clampTo (σ - p.a) p.b + clampTo (σ - p.a - p.b) p.c
    + clampTo (σ - p.a - p.b - p.c) p.d := by
  unfold U tA tB tC tD; simp; ring

theorem U_pool2 (σ : ℝ) : p.U σ 1 + p.U σ 3 = clampTo σ p.a
    + clampTo (σ - p.a) p.b + clampTo (σ - p.a - p.b) p.c := by
  unfold U tA tB tC tD; simp

/-- station-1 busy time of the unit cycle is 1-Lipschitz. -/
theorem U_pool1_lip (σ σ' : ℝ) (h : σ ≤ σ') :
    (p.U σ' 0 + p.U σ' 2 + p.U σ' 4) - (p.U σ 0 + p.U σ 2 + p.U σ 4) ≤ clampTo σ' p.L - clampTo σ p.L := by
  have hB := tB_cap hp
  have hB0 : 0 ≤ p.lam1 * p.m1 + p.m3 / p.m2 := by
    have := mul_nonneg hp.hlam.le hp.hm1.le; have := div_nonneg hp.hm3.le hp.hm2.le; linarith
  rw [U_pool1 hp, U_pool1 hp]
  have t1 := clamp_tiling hp σ
  have t2 := clamp_tiling hp σ'
  have hb := clampTo_mono (σ - p.a) (σ' - p.a) p.b (by linarith)
  nlinarith

theorem U_pool2_lip (σ σ' : ℝ) (h : σ ≤ σ') :
    (p.U σ' 1 + p.U σ' 3) - (p.U σ 1 + p.U σ 3) ≤ clampTo σ' p.L - clampTo σ p.L := by
  rw [U_pool2 hp, U_pool2 hp]
  have t1 := clamp_tiling hp σ
  have t2 := clamp_tiling hp σ'
  have hd := clampTo_mono (σ - p.a - p.b - p.c) (σ' - p.a - p.b - p.c) p.d (by linarith)
  linarith

theorem Y_A (σ : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ p.a) :
    p.Y σ = ![1 + (p.lam1 - p.phi) * σ, (p.phi - 1 / p.m2) * σ, 0, σ / p.m2, 0] := by
  have hL : σ ≤ p.L := by unfold L; linarith [b_nonneg hp, c_pos hp, d_pos hp]
  have hm1 := hp.hm1.ne'; have hm2 := hp.hm2.ne'; have hm3 := hp.hm3.ne'
  have hm4 := hp.hm4.ne'; have hm5 := hp.hm5.ne'
  unfold Y
  rw [clampTo_of_mem _ _ h0 hL]
  simp only [U_A hp σ h0 h1]
  unfold tA phi
  ext i; fin_cases i <;> simp <;> field_simp <;> ring

theorem Y_B (σ : ℝ) (h0 : p.a ≤ σ) (h1 : σ ≤ p.ab) :
    p.Y σ = ![0, p.z2 + (p.lam1 - 1 / p.m2) * (σ - p.a), 0, σ / p.m2, 0] := by
  have hL : σ ≤ p.L := by unfold L; unfold ab at h1; linarith [c_pos hp, d_pos hp]
  have hm1 := hp.hm1.ne'; have hm2 := hp.hm2.ne'; have hm3 := hp.hm3.ne'
  have hm4 := hp.hm4.ne'; have hm5 := hp.hm5.ne'
  have ha := a_eq hp
  unfold Y
  rw [clampTo_of_mem _ _ (by linarith [a_pos hp]) hL]
  simp only [U_B hp σ h0 h1]
  unfold tA tB z2 phi; unfold phi at ha
  ext i; fin_cases i <;> simp <;> field_simp <;> ring_nf <;> field_simp at ha <;> nlinarith [ha]

theorem Y_C (σ : ℝ) (h0 : p.ab ≤ σ) (h1 : σ ≤ p.abc) :
    p.Y σ = ![p.lam1 * (σ - p.a - p.b), 0, 0, p.z4 - (σ - p.a - p.b) / p.m4,
      (σ - p.a - p.b) * (1 / p.m4 - 1 / p.m5)] := by
  have hL : σ ≤ p.L := by unfold L; unfold abc at h1; linarith [d_pos hp]
  have hm1 := hp.hm1.ne'; have hm2 := hp.hm2.ne'; have hm3 := hp.hm3.ne'
  have hm4 := hp.hm4.ne'; have hm5 := hp.hm5.ne'
  have ha := a_eq hp
  have hb := b_eq hp
  have hab := ab_eq hp
  unfold Y
  rw [clampTo_of_mem _ _ (by unfold ab at h0; linarith [a_pos hp, b_nonneg hp]) hL]
  simp only [U_C hp σ h0 h1]
  unfold tA tB tC; unfold phi at ha; unfold z2 phi at hb
  ext i; fin_cases i <;> simp
  · field_simp; field_simp at ha hb; nlinarith [ha, hb]
  · field_simp; field_simp at ha hb; nlinarith [ha, hb]
  · field_simp; ring
  · rw [← hab]; field_simp
  · ring

theorem Y_D (σ : ℝ) (h0 : p.abc ≤ σ) (h1 : σ ≤ p.L) :
    p.Y σ = ![p.lam1 * (σ - p.a - p.b), 0, 0, 0,
      p.c * (1 / p.m4 - 1 / p.m5) - (σ - p.a - p.b - p.c) / p.m5] := by
  have hm1 := hp.hm1.ne'; have hm2 := hp.hm2.ne'; have hm3 := hp.hm3.ne'
  have hm4 := hp.hm4.ne'; have hm5 := hp.hm5.ne'
  have ha := a_eq hp
  have hb := b_eq hp
  have hab := ab_eq hp
  have hc := c_eq hp
  unfold Y
  rw [clampTo_of_mem _ _ (by unfold abc at h0; linarith [a_pos hp, b_nonneg hp, c_pos hp]) h1]
  simp only [U_D hp σ h0 h1]
  unfold tA tB tC tD; unfold phi at ha; unfold z2 phi at hb
  ext i; fin_cases i <;> simp
  · field_simp; field_simp at ha hb; nlinarith [ha, hb]
  · field_simp; field_simp at ha hb; nlinarith [ha, hb]
  · field_simp; ring
  · rw [← hab] at hc; field_simp; field_simp at hc; linarith [hc]
  · ring


theorem Y_zero : p.Y 0 = ![1, 0, 0, 0, 0] := by
  rw [Y_A hp 0 le_rfl (a_pos hp).le]; simp

theorem Y_L : p.Y p.L = ![p.r, 0, 0, 0, 0] := by
  rw [Y_D hp p.L (by rw [L_eq hp]; linarith [d_pos hp]) le_rfl]
  have h1 := d_eq hp
  have h2 := r_eq (p := p)
  rw [L_eq hp]; unfold abc
  ext i; fin_cases i <;> simp
  · rw [← h2]; ring
  · rw [show p.a + p.b + p.c + p.d - p.a - p.b - p.c = p.d by ring]; simp only [one_div] at h1; linarith

theorem Y_nonneg (σ : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ p.L) (i : Fin 5) : 0 ≤ p.Y σ i := by
  have hm2 := hp.hm2; have hm4 := hp.hm4; have hm5 := hp.hm5
  have hφ := phi_gt hp; have hφ' := phi_ge hp; have hi := inv_m2_gt hp
  have ha := a_eq hp; have hb := b_eq hp; have hc := c_eq hp; have hd := d_eq hp
  have hm45 : 0 ≤ 1 / p.m4 - 1 / p.m5 := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le hm4 (m5_big hp).le
  rw [sub_eq_zero, eq_div_iff hm4.ne'] at hc
  rw [sub_eq_zero, eq_div_iff hm5.ne'] at hd
  simp only [one_div] at hφ' hi hb hd hm45
  rcases le_or_gt σ p.a with hA | hA
  · rw [Y_A hp σ h0 hA]
    fin_cases i <;> simp
    · nlinarith
    · exact mul_nonneg (by linarith) h0
    · positivity
  rcases le_or_gt σ p.ab with hB | hB
  · rw [Y_B hp σ hA.le hB]; unfold ab at hB
    fin_cases i <;> simp
    · nlinarith
    · positivity
  rcases le_or_gt σ p.abc with hC | hC
  · rw [Y_C hp σ hB.le hC]; unfold ab at hB; unfold abc at hC
    fin_cases i <;> simp
    · exact mul_nonneg hp.hlam.le (by linarith)
    · rw [div_le_iff₀ hm4]; linarith
    · exact mul_nonneg (by linarith) hm45
  · rw [Y_D hp σ hC.le h1]; unfold abc at hC; rw [L_eq hp] at h1; unfold abc at h1
    fin_cases i <;> simp
    · exact mul_nonneg hp.hlam.le (by linarith [b_nonneg hp, c_pos hp])
    · rw [div_le_iff₀ hm5]; linarith

theorem Y_B_pool1 (σ : ℝ) (h0 : p.a ≤ σ) (h1 : σ ≤ p.ab) : p.Y σ 0 + p.Y σ 2 + p.Y σ 4 = 0 := by
  rw [Y_B hp σ h0 h1]; simp

theorem Y_D_pool2 (σ : ℝ) (h0 : p.abc ≤ σ) (h1 : σ ≤ p.L) : p.Y σ 1 + p.Y σ 3 = 0 := by
  rw [Y_D hp σ h0 h1]; simp

/-! ### The global self-similar solution -/

noncomputable def tn (p : RLP) (n : ℕ) : ℝ := p.L * ∑ k ∈ Finset.range n, p.r ^ k
noncomputable def Nidx (p : RLP) (t : ℝ) : ℕ := ⌈t / p.L⌉₊ + 1
noncomputable def T (p : RLP) (t : ℝ) (i : Fin 5) : ℝ :=
  ∑ k ∈ Finset.range (p.Nidx t), p.r ^ k * p.U ((t - p.tn k) / p.r ^ k) i
noncomputable def Z (p : RLP) (t : ℝ) : Fin 5 → ℝ :=
  ![1 + p.lam1 * t - p.T t 0 / p.m1, p.T t 0 / p.m1 - p.T t 1 / p.m2,
    p.T t 1 / p.m2 - p.T t 2 / p.m3, p.T t 2 / p.m3 - p.T t 3 / p.m4, p.T t 3 / p.m4 - p.T t 4 / p.m5]

theorem r_pow_pos (n : ℕ) : 0 < p.r ^ n := pow_pos (by linarith [r_ge hp]) n
theorem r_pow_ge (n : ℕ) : 1 ≤ p.r ^ n := one_le_pow₀ (r_ge hp)
omit hp in
theorem tn_zero : p.tn 0 = 0 := by simp [tn]
omit hp in
theorem tn_succ (n : ℕ) : p.tn (n + 1) = p.tn n + p.L * p.r ^ n := by
  unfold tn; rw [Finset.sum_range_succ]; ring
theorem tn_mono {n m : ℕ} (h : n ≤ m) : p.tn n ≤ p.tn m := by
  unfold tn
  refine mul_le_mul_of_nonneg_left ?_ (L_pos hp).le
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
    (fun k _ _ => (r_pow_pos hp k).le)
theorem tn_ge (n : ℕ) : (n : ℝ) * p.L ≤ p.tn n := by
  unfold tn
  have : (n : ℝ) ≤ ∑ k ∈ Finset.range n, p.r ^ k := by
    have := Finset.sum_le_sum (s := Finset.range n) (f := fun _ => (1:ℝ)) (g := fun k => p.r ^ k)
      (fun k _ => r_pow_ge hp k)
    simpa using this
  nlinarith [L_pos hp]
theorem tn_nonneg (n : ℕ) : 0 ≤ p.tn n :=
  le_trans (mul_nonneg (Nat.cast_nonneg n) (L_pos hp).le) (tn_ge hp n)
theorem tn_lt_succ (n : ℕ) : p.tn n < p.tn (n + 1) := by
  rw [tn_succ]; nlinarith [L_pos hp, r_pow_pos hp n]
theorem Nidx_ge (t : ℝ) : t ≤ p.tn (p.Nidx t) := by
  refine le_trans ?_ (tn_ge hp _)
  unfold Nidx
  have hL := L_pos hp
  rcases le_or_gt t 0 with ht | ht
  · exact le_trans ht (by positivity)
  · have h1 : t / p.L ≤ (⌈t / p.L⌉₊ : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hL] at h1
    push_cast
    nlinarith

theorem U_vanish (t : ℝ) (k : ℕ) (hk : t ≤ p.tn k) (i : Fin 5) :
    p.r ^ k * p.U ((t - p.tn k) / p.r ^ k) i = 0 := by
  rw [U_nonpos hp _ (div_nonpos_of_nonpos_of_nonneg (by linarith) (r_pow_pos hp k).le), mul_zero]

theorem T_stable (t : ℝ) (M : ℕ) (hM : t ≤ p.tn M) (i : Fin 5) :
    p.T t i = ∑ k ∈ Finset.range M, p.r ^ k * p.U ((t - p.tn k) / p.r ^ k) i := by
  unfold T
  have hv : ∀ N, t ≤ p.tn N → ∀ n ≥ N, p.r ^ n * p.U ((t - p.tn n) / p.r ^ n) i = 0 :=
    fun N hN n hn => U_vanish hp t n (hN.trans (tn_mono hp hn)) i
  rw [← Finset.eventually_constant_sum (hv _ (Nidx_ge hp t)) (le_max_left (p.Nidx t) M),
    ← Finset.eventually_constant_sum (hv _ hM) (le_max_right (p.Nidx t) M)]

theorem T_cycle (t : ℝ) (n : ℕ) (h0 : p.tn n ≤ t) (h1 : t ≤ p.tn (n + 1)) (i : Fin 5) :
    p.T t i = (∑ k ∈ Finset.range n, p.r ^ k * p.U p.L i) + p.r ^ n * p.U ((t - p.tn n) / p.r ^ n) i := by
  rw [T_stable hp t (n + 1) h1 i, Finset.sum_range_succ]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  congr 1
  apply U_ge hp
  rw [le_div_iff₀ (r_pow_pos hp k)]
  have := tn_mono hp (show k + 1 ≤ n from hk)
  rw [tn_succ] at this
  linarith

theorem T_zero (i : Fin 5) : p.T 0 i = 0 := by
  rw [T_stable hp 0 0 (by rw [tn_zero]) i]; simp

theorem exists_idx (t : ℝ) (ht : 0 ≤ t) : ∃ n, p.tn n ≤ t ∧ t < p.tn (n + 1) := by
  have hex : ∃ n, t < p.tn (n + 1) := ⟨p.Nidx t, lt_of_le_of_lt (Nidx_ge hp t) (tn_lt_succ hp _)⟩
  classical
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h, tn_zero]; exact ht
  · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push Not at this
    rwa [Nat.sub_add_cancel (by omega)] at this

theorem Z_cycle (t : ℝ) (n : ℕ) (h0 : p.tn n ≤ t) (h1 : t ≤ p.tn (n + 1)) :
    p.Z t = fun i => p.r ^ n * p.Y ((t - p.tn n) / p.r ^ n) i := by
  have hrn := r_pow_pos hp n
  set σ := (t - p.tn n) / p.r ^ n with hσ
  have hσ0 : 0 ≤ σ := div_nonneg (by linarith) hrn.le
  have hσL : σ ≤ p.L := by
    rw [hσ, div_le_iff₀ hrn]; rw [tn_succ] at h1; linarith
  have ht : t = p.tn n + p.r ^ n * σ := by rw [hσ]; field_simp; ring
  have hYL := Y_L hp
  have hgeom : (∑ k ∈ Finset.range n, p.r ^ k) * (p.r - 1) = p.r ^ n - 1 := geom_sum_mul p.r n
  have hT := fun i => T_cycle hp t n h0 h1 i
  have hsum : ∀ (c : ℝ), ∑ k ∈ Finset.range n, p.r ^ k * c = (∑ k ∈ Finset.range n, p.r ^ k) * c := by
    intro c; rw [Finset.sum_mul]
  -- components of `Y L`
  have hY0 : 1 + p.lam1 * p.L - p.U p.L 0 / p.m1 = p.r := by
    have := congrFun hYL 0; unfold Y at this; simpa [clampTo_of_mem _ _ (L_pos hp).le le_rfl] using this
  have hY1 : p.U p.L 0 / p.m1 - p.U p.L 1 / p.m2 = 0 := by
    have := congrFun hYL 1; unfold Y at this; simpa using this
  have hY2 : p.U p.L 1 / p.m2 - p.U p.L 2 / p.m3 = 0 := by
    have := congrFun hYL 2; unfold Y at this; simpa using this
  have hY3 : p.U p.L 2 / p.m3 - p.U p.L 3 / p.m4 = 0 := by
    have := congrFun hYL 3; unfold Y at this; simpa using this
  have hY4 : p.U p.L 3 / p.m4 - p.U p.L 4 / p.m5 = 0 := by
    have := congrFun hYL 4; unfold Y at this; simpa using this
  unfold Z Y
  rw [clampTo_of_mem _ _ hσ0 hσL]
  unfold tn at ht
  ext i
  fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk] <;>
    simp only [hT, hsum] <;> rw [← hσ]
  · linear_combination p.lam1 * ht + (∑ k ∈ Finset.range n, p.r ^ k) * hY0 + hgeom
  · linear_combination (∑ k ∈ Finset.range n, p.r ^ k) * hY1
  · linear_combination (∑ k ∈ Finset.range n, p.r ^ k) * hY2
  · linear_combination (∑ k ∈ Finset.range n, p.r ^ k) * hY3
  · linear_combination (∑ k ∈ Finset.range n, p.r ^ k) * hY4


omit hp in
theorem clampTo_scale (x w c : ℝ) (hc : 0 < c) (hw : 0 ≤ w) :
    c * clampTo (x / c) w = clampTo x (c * w) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [clampTo_of_nonpos _ _ (div_nonpos_of_nonpos_of_nonneg hx hc.le) hw,
      clampTo_of_nonpos _ _ hx (by positivity), mul_zero]
  rcases le_or_gt x (c * w) with hxw | hxw
  · rw [clampTo_of_mem _ _ (div_nonneg hx.le hc.le) (by rw [div_le_iff₀ hc]; linarith),
      clampTo_of_mem _ _ hx.le hxw]
    field_simp
  · rw [clampTo_of_ge _ _ (by rw [le_div_iff₀ hc]; linarith) hw, clampTo_of_ge _ _ hxw.le (by positivity)]

theorem tiling_cycles (M : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.range M, clampTo (t - p.tn k) (p.L * p.r ^ k) = clampTo t (p.tn M) := by
  induction M with
  | zero => simp [tn_zero, clampTo]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, tn_succ]
    exact clampTo_glue t _ _ (tn_nonneg hp M) (by have := L_pos hp; have := r_pow_pos hp M; positivity)

theorem T_mono (s t : ℝ) (h : s ≤ t) (i : Fin 5) : p.T s i ≤ p.T t i := by
  rw [T_stable hp t (p.Nidx t) (Nidx_ge hp t) i, T_stable hp s (p.Nidx t) (h.trans (Nidx_ge hp t)) i]
  refine Finset.sum_le_sum fun k _ => ?_
  refine mul_le_mul_of_nonneg_left (U_mono hp _ _ ?_ i) (r_pow_pos hp k).le
  exact div_le_div_of_nonneg_right (by linarith) (r_pow_pos hp k).le

theorem T_cap1 (s t : ℝ) (hs : 0 ≤ s) (h : s ≤ t) :
    (p.T t 0 + p.T t 2 + p.T t 4) - (p.T s 0 + p.T s 2 + p.T s 4) ≤ t - s := by
  have hM := Nidx_ge hp t
  rw [T_stable hp t (p.Nidx t) hM, T_stable hp t (p.Nidx t) hM, T_stable hp t (p.Nidx t) hM,
    T_stable hp s (p.Nidx t) (h.trans hM), T_stable hp s (p.Nidx t) (h.trans hM),
    T_stable hp s (p.Nidx t) (h.trans hM)]
  have key : ∀ k ∈ Finset.range (p.Nidx t),
      (p.r ^ k * p.U ((t - p.tn k) / p.r ^ k) 0 + p.r ^ k * p.U ((t - p.tn k) / p.r ^ k) 2
        + p.r ^ k * p.U ((t - p.tn k) / p.r ^ k) 4)
      - (p.r ^ k * p.U ((s - p.tn k) / p.r ^ k) 0 + p.r ^ k * p.U ((s - p.tn k) / p.r ^ k) 2
        + p.r ^ k * p.U ((s - p.tn k) / p.r ^ k) 4)
      ≤ clampTo (t - p.tn k) (p.L * p.r ^ k) - clampTo (s - p.tn k) (p.L * p.r ^ k) := by
    intro k _
    have hr := r_pow_pos hp k
    have := U_pool1_lip hp ((s - p.tn k) / p.r ^ k) ((t - p.tn k) / p.r ^ k)
      (div_le_div_of_nonneg_right (by linarith) hr.le)
    rw [mul_comm p.L, ← clampTo_scale _ _ _ hr (L_pos hp).le, ← clampTo_scale _ _ _ hr (L_pos hp).le]
    have := mul_le_mul_of_nonneg_left this hr.le
    linarith
  have hsum := Finset.sum_le_sum key
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [tiling_cycles hp, tiling_cycles hp, clampTo_of_mem _ _ (hs.trans h) hM,
    clampTo_of_mem _ _ hs (h.trans hM)] at hsum
  linarith

theorem T_cap2 (s t : ℝ) (hs : 0 ≤ s) (h : s ≤ t) :
    (p.T t 1 + p.T t 3) - (p.T s 1 + p.T s 3) ≤ t - s := by
  have hM := Nidx_ge hp t
  rw [T_stable hp t (p.Nidx t) hM, T_stable hp t (p.Nidx t) hM,
    T_stable hp s (p.Nidx t) (h.trans hM), T_stable hp s (p.Nidx t) (h.trans hM)]
  have key : ∀ k ∈ Finset.range (p.Nidx t),
      (p.r ^ k * p.U ((t - p.tn k) / p.r ^ k) 1 + p.r ^ k * p.U ((t - p.tn k) / p.r ^ k) 3)
      - (p.r ^ k * p.U ((s - p.tn k) / p.r ^ k) 1 + p.r ^ k * p.U ((s - p.tn k) / p.r ^ k) 3)
      ≤ clampTo (t - p.tn k) (p.L * p.r ^ k) - clampTo (s - p.tn k) (p.L * p.r ^ k) := by
    intro k _
    have hr := r_pow_pos hp k
    have := U_pool2_lip hp ((s - p.tn k) / p.r ^ k) ((t - p.tn k) / p.r ^ k)
      (div_le_div_of_nonneg_right (by linarith) hr.le)
    rw [mul_comm p.L, ← clampTo_scale _ _ _ hr (L_pos hp).le, ← clampTo_scale _ _ _ hr (L_pos hp).le]
    have := mul_le_mul_of_nonneg_left this hr.le
    linarith
  have hsum := Finset.sum_le_sum key
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [tiling_cycles hp, tiling_cycles hp, clampTo_of_mem _ _ (hs.trans h) hM,
    clampTo_of_mem _ _ hs (h.trans hM)] at hsum
  linarith

/-- Local affine behaviour of `T` to the right of `t`, inside a phase. -/
theorem T_affine (t : ℝ) (n : ℕ) (lo hi : ℝ) (base rate : Fin 5 → ℝ) (h0 : p.tn n ≤ t)
    (hlo : lo ≤ (t - p.tn n) / p.r ^ n) (hhi : (t - p.tn n) / p.r ^ n < hi) (hhiL : hi ≤ p.L)
    (hU : ∀ σ', lo ≤ σ' → σ' ≤ hi → ∀ i, p.U σ' i = base i + rate i * (σ' - lo)) :
    ∃ η > 0, ∀ h, 0 ≤ h → h ≤ η → ∀ i, p.T (t + h) i = p.T t i + rate i * h := by
  have hr := r_pow_pos hp n
  set σ := (t - p.tn n) / p.r ^ n with hσ
  refine ⟨(hi - σ) * p.r ^ n, by nlinarith, fun h hh0 hhη i => ?_⟩
  have hσ' : (t + h - p.tn n) / p.r ^ n = σ + h / p.r ^ n := by rw [hσ]; ring
  have hle : σ + h / p.r ^ n ≤ hi := by
    rw [← sub_nonneg]
    have : hi - (σ + h / p.r ^ n) = ((hi - σ) * p.r ^ n - h) / p.r ^ n := by field_simp; ring
    rw [this]; exact div_nonneg (by linarith) hr.le
  have h1 : t ≤ p.tn (n + 1) := by
    rw [tn_succ]
    have : σ < p.L := lt_of_lt_of_le hhi hhiL
    rw [hσ, div_lt_iff₀ hr] at this; linarith
  have h1' : t + h ≤ p.tn (n + 1) := by
    rw [tn_succ]
    have : σ + h / p.r ^ n ≤ p.L := hle.trans hhiL
    rw [hσ, ← sub_nonneg] at this
    have e : p.L - ((t - p.tn n) / p.r ^ n + h / p.r ^ n) = (p.L * p.r ^ n - (t - p.tn n) - h) / p.r ^ n := by
      field_simp; ring
    rw [e] at this
    have := (div_nonneg_iff.mp this).resolve_right (fun h' => absurd hr (not_lt.mpr h'.2))
    linarith
  rw [T_cycle hp (t + h) n (by linarith) h1' i, T_cycle hp t n h0 h1 i, hσ', ← hσ,
    hU (σ + h / p.r ^ n) (by linarith [div_nonneg hh0 hr.le]) hle i, hU σ hlo hhi.le i]
  have e : p.r ^ n * (h / p.r ^ n) = h := by field_simp
  linear_combination rate i * e

omit hp in
theorem right_slope_unique (g : ℝ → ℝ) (t d c η : ℝ) (hη : 0 < η)
    (h : ∀ h', 0 ≤ h' → h' ≤ η → g (t + h') = g t + c * h') (hd : HasDerivAt g d t) : d = c := by
  have h1 := hd.tendsto_slope_zero_right
  have h2 : Tendsto (fun h' : ℝ => h'⁻¹ • (g (t + h') - g t)) (𝓝[>] 0) (𝓝 c) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hη] with h' hh'
    rw [h h' hh'.1.le hh'.2.le, smul_eq_mul]
    field_simp [hh'.1.ne']
    ring
  exact tendsto_nhds_unique h1 h2


theorem T_phase (t : ℝ) (ht : 0 ≤ t) : ∃ η > 0, ∃ rate : Fin 5 → ℝ,
    (∀ h, 0 ≤ h → h ≤ η → ∀ i, p.T (t + h) i = p.T t i + rate i * h) ∧
    (rate 0 + rate 2 + rate 4 = 1 ∨ p.Z t 0 + p.Z t 2 + p.Z t 4 = 0) ∧
    (rate 1 + rate 3 = 1 ∨ p.Z t 1 + p.Z t 3 = 0) := by
  obtain ⟨n, h0, h1⟩ := exists_idx hp t ht
  have hrn := r_pow_pos hp n
  have hZ := Z_cycle hp t n h0 h1.le
  set σ := (t - p.tn n) / p.r ^ n with hσ
  have hσ0 : 0 ≤ σ := div_nonneg (by linarith) hrn.le
  have hσL : σ < p.L := by
    rw [hσ, div_lt_iff₀ hrn]; rw [tn_succ] at h1; linarith
  have hab : p.ab = p.a + p.b := rfl
  have habc : p.abc = p.a + p.b + p.c := rfl
  have hLe : p.L = p.a + p.b + p.c + p.d := rfl
  have hm2 := hp.hm2.ne'
  rcases lt_or_ge σ p.a with hA | hA
  · obtain ⟨η, hη, hT⟩ := T_affine hp t n 0 p.a (fun _ => 0) p.tA h0 hσ0 hA
      (by rw [hLe]; linarith [b_nonneg hp, c_pos hp, d_pos hp])
      (fun σ' h0' h1' i => by rw [U_A hp σ' h0' h1']; ring)
    refine ⟨η, hη, p.tA, hT, Or.inl ?_, Or.inl ?_⟩ <;> unfold tA <;> simp <;> ring
  rcases lt_or_ge σ p.ab with hB | hB
  · obtain ⟨η, hη, hT⟩ := T_affine hp t n p.a p.ab (fun i => p.tA i * p.a) p.tB h0 hA hB
      (by rw [hLe, hab]; linarith [c_pos hp, d_pos hp])
      (fun σ' h0' h1' i => by rw [U_B hp σ' h0' h1'])
    refine ⟨η, hη, p.tB, hT, Or.inr ?_, Or.inl ?_⟩
    · simp only [hZ]
      rw [← mul_add, ← mul_add, Y_B_pool1 hp σ hA hB.le, mul_zero]
    · unfold tB; simp
  rcases lt_or_ge σ p.abc with hC | hC
  · obtain ⟨η, hη, hT⟩ := T_affine hp t n p.ab p.abc (fun i => p.tA i * p.a + p.tB i * p.b) p.tC h0 hB hC
      (by rw [hLe, habc]; linarith [d_pos hp])
      (fun σ' h0' h1' i => by rw [U_C hp σ' h0' h1', hab]; ring)
    refine ⟨η, hη, p.tC, hT, Or.inl ?_, Or.inl ?_⟩ <;> unfold tC <;> simp
  · obtain ⟨η, hη, hT⟩ := T_affine hp t n p.abc p.L (fun i => p.tA i * p.a + p.tB i * p.b + p.tC i * p.c)
      p.tD h0 hC hσL le_rfl
      (fun σ' h0' h1' i => by rw [U_D hp σ' h0' h1', habc]; ring)
    refine ⟨η, hη, p.tD, hT, Or.inl ?_, Or.inr ?_⟩
    · unfold tD; simp
    · simp only [hZ]
      rw [← mul_add, Y_D_pool2 hp σ hC hσL.le, mul_zero]

theorem Z_zero : p.Z 0 = ![1, 0, 0, 0, 0] := by
  unfold Z; simp [T_zero hp]

theorem cycle_solution :
    IsNonIdlingSolution p.dat (fun t i => p.T t i / p.mv i) (fun t i => p.T t i / p.mv i) p.T p.Z := by
  have hmpos : ∀ i, 0 < p.mv i := by
    intro i; unfold mv; fin_cases i <;> simp [hp.hm1, hp.hm2, hp.hm3, hp.hm4, hp.hm5]
  have hZ0 := Z_zero hp
  refine ⟨⟨?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro t ht i
    unfold dat
    rw [rl_route_sum, rl_lam, hZ0]
    unfold Z mv
    fin_cases i <;> simp
  · intro t ht i
    obtain ⟨n, h0, h1⟩ := exists_idx hp t ht
    rw [Z_cycle hp t n h0 h1.le]
    have hrn := r_pow_pos hp n
    refine mul_nonneg hrn.le (Y_nonneg hp _ (div_nonneg (by linarith) hrn.le) ?_ i)
    rw [div_le_iff₀ hrn]; rw [tn_succ] at h1; linarith
  · intro t ht i; rfl
  · intro t ht i
    unfold dat; rw [rl_m]
    have := (hmpos i).ne'
    unfold mv at this ⊢
    field_simp
  · funext i; exact T_zero hp i
  · intro s t hst i
    exact T_mono hp s t hst i
  · intro s t hs hst k
    unfold dat; rw [rl_pool_sum, rl_b]
    fin_cases k <;> simp
    · have := T_cap1 hp s t hs hst; linarith
    · have := T_cap2 hp s t hs hst; linarith
  · intro k t ht hpos d hd
    unfold dat at hpos hd ⊢
    simp only [rl_pool_sum, rl_b] at hpos hd ⊢
    obtain ⟨η, hη, rate, hT, hp1, hp2⟩ := T_phase hp t ht.le
    fin_cases k <;> simp at hpos hd ⊢
    · have := right_slope_unique (fun s => p.T s 0 + p.T s 2 + p.T s 4) t d (rate 0 + rate 2 + rate 4) η hη
        (fun h' hh0 hhη => by show _ = _; rw [hT h' hh0 hhη, hT h' hh0 hhη, hT h' hh0 hhη]; ring) hd
      rcases hp1 with h | h
      · rw [this, h]
      · linarith
    · have := right_slope_unique (fun s => p.T s 1 + p.T s 3) t d (rate 1 + rate 3) η hη
        (fun h' hh0 hhη => by show _ = _; rw [hT h' hh0 hhη, hT h' hh0 hhη]; ring) hd
      rcases hp2 with h | h
      · rw [this, h]
      · linarith

theorem not_stable : ¬ FluidModelGloballyStable p.dat := by
  rintro ⟨γ, hγ, hall⟩
  have hsol := cycle_solution hp
  set N := ⌈γ / p.L⌉₊ with hN
  have hL := L_pos hp
  have hNγ : γ ≤ p.tn N := by
    refine le_trans ?_ (tn_ge hp N)
    have : γ / p.L ≤ (N : ℝ) := Nat.le_ceil _
    rwa [div_le_iff₀ hL] at this
  have hsum : ∑ i, p.Z 0 i = 1 := by rw [Z_zero hp]; simp [Fin.sum_univ_five]
  have h := hall _ _ _ _ hsol (p.tn N) (by rw [hsum, mul_one]; exact hNγ)
  have hZ := Z_cycle hp (p.tn N) N le_rfl (tn_lt_succ hp N).le
  rw [h] at hZ
  have := congrFun hZ 0
  simp only [sub_self, zero_div, Y_zero hp] at this
  simp at this
  exact (r_pow_pos hp N).ne' this.symm

end RLP

theorem rl_unstable_vs_cycle (lam1 m1 m2 m3 m4 m5 : ℝ) (hlam1 : 0 < lam1)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm3 : 0 < m3) (hm4 : 0 < m4) (hm5 : 0 < m5)
    (hc1 : lam1 * (m1 + m3 + m5) < 1) (hc2 : lam1 * (m2 + m4) < 1)
    (hvs : 1 ≤ lam1 * (m2 + m5)) (hlt : lam1 * m1 * m2 < m2 - m3) :
    ¬ FluidModelGloballyStable (reentrantLineData lam1 m1 m2 m3 m4 m5) :=
  RLP.not_stable (p := ⟨lam1, m1, m2, m3, m4, m5⟩) ⟨hlam1, hm1, hm2, hm3, hm4, hm5, hc1, hc2, hvs, hlt⟩

/-- Existence of the piecewise-linear Lyapunov coefficients. -/
theorem rl_exists_x (lam1 m1 m2 m3 m4 m5 : ℝ) (hlam1 : 0 < lam1)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm3 : 0 < m3) (hm4 : 0 < m4) (hm5 : 0 < m5)
    (hc1 : lam1 * (m1 + m3 + m5) < 1) (hc2 : lam1 * (m2 + m4) < 1) (hc3 : lam1 * (m2 + m5) < 1) :
    ∃ x1 x2 x3 x4 x5 : ℝ, 0 < x5 ∧ x5 < x4 ∧ x4 < x3 + x5 ∧ x3 + x5 < x2 + x4 ∧
      x2 + x4 < x1 + x3 + x5 ∧
      lam1 * (x1 + x3 + x5) * m1 < x1 ∧ lam1 * (x1 + x3 + x5) * m3 < x3 ∧
      lam1 * (x1 + x3 + x5) * m5 < x5 ∧
      lam1 * (x2 + x4) * m2 < x2 ∧ lam1 * (x2 + x4) * m4 < x4 := by
  have p1 := mul_pos hlam1 hm1; have p2 := mul_pos hlam1 hm2; have p3 := mul_pos hlam1 hm3
  have p4 := mul_pos hlam1 hm4; have p5 := mul_pos hlam1 hm5
  set L1 := 1 - lam1 * m1 with hL1
  have hL1pos : 0 < L1 := by rw [hL1]; nlinarith
  have hL1' : lam1 * (m3 + m5) < L1 := by rw [hL1]; linarith
  have hA : lam1 * m4 < 1 := by linarith
  have hA' : lam1 * m4 < 1 - lam1 * m2 := by linarith
  have hB' : lam1 * m5 < L1 := by rw [hL1]; linarith
  have h12 : 0 < 1 - lam1 * m2 := by linarith
  -- choose σ
  set slo := max 1 (lam1 * m4 / L1) with hslo
  set shi := min (1 / (lam1 * (m3 + m5))) ((1 - lam1 * m2) / (lam1 * m5)) with hshi
  have h35 : 0 < lam1 * (m3 + m5) := by positivity
  have hlm5 : 0 < lam1 * m5 := by positivity
  have hlt1 : slo < shi := by
    rw [hslo, hshi]
    refine max_lt (lt_min ?_ ?_) (lt_min ?_ ?_)
    · rw [lt_div_iff₀ h35]; linarith
    · rw [lt_div_iff₀ hlm5]; linarith
    · rw [div_lt_div_iff₀ hL1pos h35]
      have := mul_lt_mul_of_pos_right hA h35; linarith
    · rw [div_lt_div_iff₀ hL1pos hlm5]
      have := mul_lt_mul_of_pos_right hA' hlm5
      have := mul_lt_mul_of_pos_left hB' h12
      linarith
  set σ := (slo + shi) / 2 with hσ
  have hσ1 : 1 < σ := by
    have : 1 ≤ slo := le_max_left _ _
    rw [hσ]; linarith
  have hσ2 : lam1 * m4 < σ * L1 := by
    have : lam1 * m4 / L1 ≤ slo := le_max_right _ _
    have : lam1 * m4 / L1 < σ := by rw [hσ]; linarith
    rwa [div_lt_iff₀ hL1pos] at this
  have hσ3 : lam1 * (m3 + m5) * σ < 1 := by
    have : shi ≤ 1 / (lam1 * (m3 + m5)) := min_le_left _ _
    have : σ < 1 / (lam1 * (m3 + m5)) := by rw [hσ]; linarith
    rw [lt_div_iff₀ h35] at this; linarith
  have hσ4 : lam1 * m5 * σ < 1 - lam1 * m2 := by
    have : shi ≤ (1 - lam1 * m2) / (lam1 * m5) := min_le_right _ _
    have : σ < (1 - lam1 * m2) / (lam1 * m5) := by rw [hσ]; linarith
    rw [lt_div_iff₀ hlm5] at this; linarith
  have hσpos : 0 < σ := by linarith
  -- choose x4
  set lo4 := max (lam1 * m5 * σ) (lam1 * m4) with hlo4
  set hi4 := min (1 - lam1 * m2) (σ * L1) with hhi4
  have hlt4 : lo4 < hi4 := by
    rw [hlo4, hhi4]
    refine max_lt (lt_min ?_ ?_) (lt_min ?_ ?_)
    · linarith
    · have := mul_lt_mul_of_pos_left hB' hσpos; linarith
    · linarith
    · linarith
  set x4 := (lo4 + hi4) / 2 with hx4
  have hx4a : lam1 * m5 * σ < x4 := by
    have : lam1 * m5 * σ ≤ lo4 := le_max_left _ _
    rw [hx4]; linarith
  have hx4b : lam1 * m4 < x4 := by
    have : lam1 * m4 ≤ lo4 := le_max_right _ _
    rw [hx4]; linarith
  have hx4c : x4 < 1 - lam1 * m2 := by
    have : hi4 ≤ 1 - lam1 * m2 := min_le_left _ _
    rw [hx4]; linarith
  have hx4d : x4 < σ * L1 := by
    have : hi4 ≤ σ * L1 := min_le_right _ _
    rw [hx4]; linarith
  set x2 := 1 - x4 with hx2
  -- choose u = x3 + x5
  set lou := max x4 (lam1 * (m3 + m5) * σ) with hlou
  set hiu := min 1 (σ * L1) with hhiu
  have hltu : lou < hiu := by
    rw [hlou, hhiu]
    refine max_lt (lt_min ?_ ?_) (lt_min ?_ ?_)
    · linarith
    · linarith
    · linarith
    · have := mul_lt_mul_of_pos_left hL1' hσpos; linarith
  set u := (lou + hiu) / 2 with hu
  have hua : x4 < u := by
    have : x4 ≤ lou := le_max_left _ _
    rw [hu]; linarith
  have hub : lam1 * (m3 + m5) * σ < u := by
    have : lam1 * (m3 + m5) * σ ≤ lou := le_max_right _ _
    rw [hu]; linarith
  have huc : u < 1 := by
    have : hiu ≤ 1 := min_le_left _ _
    rw [hu]; linarith
  have hud : u < σ * L1 := by
    have : hiu ≤ σ * L1 := min_le_right _ _
    rw [hu]; linarith
  set δ := min (u - lam1 * (m3 + m5) * σ) (x4 - lam1 * m5 * σ) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; exact half_pos (lt_min (by linarith) (by linarith))
  have hδ1 : δ < u - lam1 * (m3 + m5) * σ := by
    have : min (u - lam1 * (m3 + m5) * σ) (x4 - lam1 * m5 * σ) ≤ u - lam1 * (m3 + m5) * σ := min_le_left _ _
    rw [hδ]; linarith
  have hδ2 : δ < x4 - lam1 * m5 * σ := by
    have : min (u - lam1 * (m3 + m5) * σ) (x4 - lam1 * m5 * σ) ≤ x4 - lam1 * m5 * σ := min_le_right _ _
    rw [hδ]; linarith
  refine ⟨σ - u, x2, u - (lam1 * m5 * σ + δ), x4, lam1 * m5 * σ + δ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · linarith
  · linarith
  · rw [hx2]; linarith
  · rw [hx2]; linarith
  · have : σ - u + (u - (lam1 * m5 * σ + δ)) + (lam1 * m5 * σ + δ) = σ := by ring
    rw [this, hL1] at *; nlinarith
  · have : σ - u + (u - (lam1 * m5 * σ + δ)) + (lam1 * m5 * σ + δ) = σ := by ring
    rw [this]; nlinarith
  · have : σ - u + (u - (lam1 * m5 * σ + δ)) + (lam1 * m5 * σ + δ) = σ := by ring
    rw [this]; linarith
  · have : x2 + x4 = 1 := by rw [hx2]; ring
    rw [this, hx2]; linarith
  · have : x2 + x4 = 1 := by rw [hx2]; ring
    rw [this]; linarith

theorem reentrant_line_core (lam1 m1 m2 m3 m4 m5 : ℝ) (hlam1 : 0 < lam1)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm3 : 0 < m3) (hm4 : 0 < m4) (hm5 : 0 < m5) :
    FluidModelGloballyStable (reentrantLineData lam1 m1 m2 m3 m4 m5) ↔
      (lam1 * (m1 + m3 + m5) < 1 ∧ lam1 * (m2 + m4) < 1 ∧ lam1 * (m2 + m5) < 1) := by
  constructor
  · intro hst
    by_cases hc1 : lam1 * (m1 + m3 + m5) < 1
    · by_cases hc2 : lam1 * (m2 + m4) < 1
      · by_cases hc3 : lam1 * (m2 + m5) < 1
        · exact ⟨hc1, hc2, hc3⟩
        · exfalso
          push Not at hc3
          by_cases hlin : m2 - m3 ≤ lam1 * m1 * m2
          · exact rl_unstable_vs_linear lam1 m1 m2 m3 m4 m5 hlam1 hm1 hm2 hm3 hm4 hm5 hc1 hc2 hc3 hlin hst
          · push Not at hlin
            exact rl_unstable_vs_cycle lam1 m1 m2 m3 m4 m5 hlam1 hm1 hm2 hm3 hm4 hm5 hc1 hc2 hc3 hlin hst
      · exfalso
        push Not at hc2
        exact rl_unstable_load lam1 m1 m2 m3 m4 m5 hlam1 hm1 hm2 hm3 hm4 hm5 (Or.inr hc2) hst
    · exfalso
      push Not at hc1
      exact rl_unstable_load lam1 m1 m2 m3 m4 m5 hlam1 hm1 hm2 hm3 hm4 hm5 (Or.inl hc1) hst
  · rintro ⟨hc1, hc2, hc3⟩
    obtain ⟨x1, x2, x3, x4, x5, hx5, h54, h435, h2435, hS, b1, b3, b5, b2, b4⟩ :=
      rl_exists_x lam1 m1 m2 m3 m4 m5 hlam1 hm1 hm2 hm3 hm4 hm5 hc1 hc2 hc3
    exact rl_stable_of_conditions lam1 m1 m2 m3 m4 m5 hlam1 hm1 hm2 hm3 hm4 hm5 x1 x2 x3 x4 x5
      hx5 h54 h435 h2435 hS b1 b3 b5 b2 b4

end ProcessingNetworks.GlobalStability

open ProcessingNetworks.GlobalStability


theorem solution
    (lam1 m1 m2 m3 m4 m5 : ℝ) (hlam1 : 0 < lam1)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm3 : 0 < m3) (hm4 : 0 < m4) (hm5 : 0 < m5) :
    FluidModelGloballyStable (reentrantLineData lam1 m1 m2 m3 m4 m5) ↔
      (lam1 * (m1 + m3 + m5) < 1 ∧ lam1 * (m2 + m4) < 1 ∧ lam1 * (m2 + m5) < 1) := by
  exact reentrant_line_core lam1 m1 m2 m3 m4 m5 hlam1 hm1 hm2 hm3 hm4 hm5
