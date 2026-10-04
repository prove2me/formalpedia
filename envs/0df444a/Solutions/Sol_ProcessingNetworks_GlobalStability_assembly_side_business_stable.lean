-- Prove2me | solution 1 for ProcessingNetworks.GlobalStability.assembly_side_business_stable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:12:40.581747+00:00
-- url     : https://prove2.me/submissions/5cbd51e7-3a37-4044-9086-3583331c1097

import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_AssemblySideBusiness

open MeasureTheory Filter Topology Set

namespace ProcessingNetworks.GlobalStability.ASB

noncomputable def diniUpperRight (f : ℝ → ℝ) (t : ℝ) : EReal :=
  Filter.limsup (fun h : ℝ => (((f (t + h) - f t) / h : ℝ) : EReal))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

theorem dec_dini_of_hasDerivAt (f : ℝ → ℝ) (d t : ℝ) (h : HasDerivAt f d t) :
    diniUpperRight f t = (d : EReal) := by
  have h1 := h.tendsto_slope_zero_right
  have h2 : Tendsto (fun s : ℝ => (((f (t + s) - f t) / s : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (d : EReal)) :=
    (continuous_coe_real_ereal.tendsto d).comp (h1.congr fun s => by
      simp [smul_eq_mul, div_eq_inv_mul])
  exact h2.limsup_eq

theorem dec_freq (f : ℝ → ℝ) (x M : ℝ) (hD : diniUpperRight f x ≤ (M : EReal)) (r : ℝ)
    (hr : M < r) : ∃ᶠ z in 𝓝[>] x, slope f x z < r := by
  have hlt : diniUpperRight f x < (r : EReal) := lt_of_le_of_lt hD (EReal.coe_lt_coe_iff.mpr hr)
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

theorem dec_upper (f : ℝ → ℝ) (a b M : ℝ) (hc : ContinuousOn f (Icc a b))
    (hD : ∀ t ∈ Ico a b, diniUpperRight f t ≤ (M : EReal)) :
    ∀ x ∈ Icc a b, f x ≤ f a + M * (x - a) := by
  intro x hx
  refine le_of_forall_pos_le_add fun η hη => ?_
  set δ := η / (x - a + 1) with hδ
  have hxa : 0 ≤ x - a := sub_nonneg.mpr hx.1
  have hδpos : 0 < δ := by positivity
  have key := image_le_of_liminf_slope_right_lt_deriv_boundary' (f' := fun _ => M) hc
    (fun t ht r hr => dec_freq f t M (hD t ht) r hr)
    (B := fun t => f a + (M + δ) * (t - a)) (B' := fun _ => M + δ) (by simp)
    (by fun_prop)
    (fun t _ => (((hasDerivAt_id t).sub_const a).const_mul (M + δ)).const_add (f a)
      |>.hasDerivWithinAt |>.congr_deriv (by simp))
    (fun t _ _ => by linarith) hx
  have : δ * (x - a) ≤ η := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

theorem dec_mono (f : ℝ → ℝ) (a b M : ℝ) (hc : ContinuousOn f (Icc a b))
    (hD : ∀ t ∈ Ico a b, diniUpperRight f t ≤ (M : EReal)) :
    MonotoneOn (fun t => M * t - f t) (Icc a b) := by
  intro x hx y hy hxy
  have := dec_upper f x y M (hc.mono (Icc_subset_Icc hx.1 hy.2))
    (fun t ht => hD t ⟨hx.1.trans ht.1, lt_of_lt_of_le ht.2 hy.2⟩) y ⟨hxy, le_rfl⟩
  simp only
  linarith

theorem dec_decrease (f : ℝ → ℝ) (a b M ε : ℝ) (ha : 0 < a) (hab : a < b)
    (hc : ContinuousOn f (Icc a b))
    (hD : ∀ t ∈ Ico a b, diniUpperRight f t ≤ (M : EReal))
    (hpos : ∀ t ∈ Ioo a b, 0 < f t)
    (hdrift : ∀ᵐ t, 0 ≤ t → 0 < f t → diniUpperRight f t ≤ ((-ε : ℝ) : EReal)) :
    f b ≤ f a - ε * (b - a) := by
  set h : ℝ → ℝ := fun t => M * t - f t with hh
  have hmono : MonotoneOn h (Icc a b) := dec_mono f a b M hc hD
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
    rw [dec_dini_of_hasDerivAt f _ x hfd, EReal.coe_le_coe_iff] at this
    show M + ε ≤ deriv h x
    linarith
  have hmono_int := intervalIntegral.integral_mono_ae_restrict hab.le
    intervalIntegrable_const hii hlow
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hmono_int
  have := hint.2
  simp only [hh] at this
  nlinarith

theorem dec_induct (f : ℝ → ℝ) (hcont : ContinuousOn f (Ioi 0))
    (hbound : ∀ a b : ℝ, 0 ≤ a → a < b → ∃ M : ℝ, 0 < M ∧ ∀ t ∈ Ico a b, diniUpperRight f t ≤ (M : EReal))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hdrift : ∀ᵐ t, 0 ≤ t → 0 < f t → diniUpperRight f t ≤ ((-ε : ℝ) : EReal))
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
        have hdec := dec_decrease f y z M ε hy0 hz.1
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

theorem dec_main
    (f : ℝ → ℝ) (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t)
    (hcont : ContinuousOn f (Set.Ioi 0))
    (hbound : ∀ a b : ℝ, 0 ≤ a → a < b → ∃ M : ℝ, 0 < M ∧ ∀ t ∈ Set.Ico a b, diniUpperRight f t ≤ (M : EReal))
    (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ᵐ t, 0 ≤ t → 0 < f t → diniUpperRight f t ≤ ((-ε : ℝ) : EReal)) :
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
  have hD : diniUpperRight f 0 < ((M0 + 1 : ℝ) : EReal) :=
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
  have key := dec_induct f hcont hbound ε hε.le hdrift a (η / 2) (f 0 + (M0 + 1) * a + ε * a) hapos
    (by positivity) hfa t (le_trans ha2.2.le (min_le_left _ _))
  have hac : a * K ≤ η / 2 := by
    have : a ≤ η / (2 * K) := le_trans ha2.2.le (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have : f 0 + (M0 + 1) * a + ε * a - ε * t ≤ η / 2 := by nlinarith
  have := max_le (le_refl (η / 2)) this
  linarith


theorem asb_lip (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (h : ∀ s t, 0 ≤ s → s ≤ t → |f t - f s| ≤ L * (t - s)) :
    LipschitzOnWith (Real.toNNReal L) f (Ici 0) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [Real.coe_toNNReal _ hL, Real.dist_eq, Real.dist_eq]
  rcases le_total x y with hxy | hxy
  · have := h x y hx hxy
    rw [abs_sub_comm (f x) (f y), abs_sub_comm x y, abs_of_nonneg (by linarith : 0 ≤ y - x)]
    exact this
  · have := h y x hy hxy
    rw [abs_of_nonneg (by linarith : 0 ≤ x - y)]
    exact this

end ProcessingNetworks.GlobalStability.ASB

open ProcessingNetworks.GlobalStability ProcessingNetworks.GlobalStability.ASB in
theorem solution
    (lam1 lam2 m1 m2 : ℝ) (hm1 : 0 < m1) (hm2 : 0 < m2)
    (h1 : lam2 > lam1) (h2 : lam1 * m1 < 1) (h3 : (lam2 - lam1) * m2 < 1) :
    AssemblySideBusinessFluidStable lam1 lam2 m1 m2 := by
  have k1 : lam1 < 1 / m1 := by rw [lt_div_iff₀ hm1]; linarith
  have k2 : lam2 - lam1 < 1 / m2 := by rw [lt_div_iff₀ hm2]; linarith
  set η := min (min (1 / m1 - lam1) (lam2 - lam1)) (min (1 / m1 + 1 / m2 - lam2) (lam1 + 1 / m2 - lam2))
    with hη
  have hηpos : 0 < η := by
    rw [hη]
    refine lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))
  have e1 : η ≤ 1 / m1 - lam1 := (min_le_left _ _).trans (min_le_left _ _)
  have e2 : η ≤ lam2 - lam1 := (min_le_left _ _).trans (min_le_right _ _)
  have e3 : η ≤ 1 / m1 + 1 / m2 - lam2 := (min_le_right _ _).trans (min_le_left _ _)
  have e4 : η ≤ lam1 + 1 / m2 - lam2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨1 / η, by positivity, fun Z1 Z2 Ta Ts hsol t ht => ?_⟩
  obtain ⟨hz1, hz2, ⟨hTa0, hTs0⟩, hTa, hTs, hnn, hd7, hd8, hd9, -⟩ := hsol
  set V : ℝ → ℝ := fun s => max (Z1 s) (Z2 s) with hV
  -- increments
  have inc1 : ∀ s u, 0 ≤ s → s ≤ u → Z1 u - Z1 s = lam1 * (u - s) - (Ta u - Ta s) / m1 := by
    intro s u hs hsu; rw [hz1 u (hs.trans hsu), hz1 s hs]; ring
  have inc2 : ∀ s u, 0 ≤ s → s ≤ u →
      Z2 u - Z2 s = lam2 * (u - s) - (Ta u - Ta s) / m1 - (Ts u - Ts s) / m2 := by
    intro s u hs hsu; rw [hz2 u (hs.trans hsu), hz2 s hs]; ring
  have L1 : ∀ s u, 0 ≤ s → s ≤ u → |Z1 u - Z1 s| ≤ (|lam1| + 1 / m1) * (u - s) := by
    intro s u hs hsu
    rw [inc1 s u hs hsu]
    have hw : 0 ≤ u - s := by linarith
    have ha := hTa s u hs hsu
    have hd : 0 ≤ (Ta u - Ta s) / m1 := div_nonneg ha.1 hm1.le
    have hd' : (Ta u - Ta s) / m1 ≤ 1 / m1 * (u - s) := by
      rw [div_eq_mul_one_div, mul_comm]; exact mul_le_mul_of_nonneg_left ha.2 (by positivity)
    have p1 : lam1 * (u - s) ≤ |lam1| * (u - s) := mul_le_mul_of_nonneg_right (le_abs_self _) hw
    have p2 : -(|lam1| * (u - s)) ≤ lam1 * (u - s) := by
      have := mul_le_mul_of_nonneg_right (neg_abs_le lam1) hw; linarith
    rw [add_mul, abs_le]
    constructor <;> linarith
  have L2 : ∀ s u, 0 ≤ s → s ≤ u → |Z2 u - Z2 s| ≤ (|lam2| + 1 / m1 + 1 / m2) * (u - s) := by
    intro s u hs hsu
    rw [inc2 s u hs hsu]
    have hw : 0 ≤ u - s := by linarith
    have ha := hTa s u hs hsu
    have hb := hTs s u hs hsu
    have hd : 0 ≤ (Ta u - Ta s) / m1 := div_nonneg ha.1 hm1.le
    have hd' : (Ta u - Ta s) / m1 ≤ 1 / m1 * (u - s) := by
      rw [div_eq_mul_one_div, mul_comm]; exact mul_le_mul_of_nonneg_left ha.2 (by positivity)
    have he : 0 ≤ (Ts u - Ts s) / m2 := div_nonneg hb.1 hm2.le
    have he' : (Ts u - Ts s) / m2 ≤ 1 / m2 * (u - s) := by
      rw [div_eq_mul_one_div, mul_comm]; exact mul_le_mul_of_nonneg_left hb.2 (by positivity)
    have p1 : lam2 * (u - s) ≤ |lam2| * (u - s) := mul_le_mul_of_nonneg_right (le_abs_self _) hw
    have p2 : -(|lam2| * (u - s)) ≤ lam2 * (u - s) := by
      have := mul_le_mul_of_nonneg_right (neg_abs_le lam2) hw; linarith
    rw [add_mul, add_mul, abs_le]
    constructor <;> linarith
  have LV : ∀ s u, 0 ≤ s → s ≤ u → |V u - V s| ≤
      ((|lam1| + 1 / m1) + (|lam2| + 1 / m1 + 1 / m2)) * (u - s) := by
    intro s u hs hsu
    have := abs_max_sub_max_le_max (Z1 u) (Z2 u) (Z1 s) (Z2 s)
    have q1 := L1 s u hs hsu
    have q2 := L2 s u hs hsu
    have hm : max |Z1 u - Z1 s| |Z2 u - Z2 s| ≤ |Z1 u - Z1 s| + |Z2 u - Z2 s| :=
      max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
    rw [add_mul]
    simp only [hV]
    linarith
  have hlip1 := asb_lip Z1 _ (by positivity) L1
  have hlip2 := asb_lip Z2 _ (by positivity) L2
  have hlipV := asb_lip V _ (by positivity) LV
  have hVnn : ∀ s, 0 ≤ s → 0 ≤ V s := fun s hs => le_max_of_le_left (hnn s hs).1
  have hVcont : ContinuousOn V (Ioi 0) := hlipV.continuousOn.mono Ioi_subset_Ici_self
  have hbound : ∀ a b : ℝ, 0 ≤ a → a < b → ∃ M : ℝ, 0 < M ∧
      ∀ s ∈ Set.Ico a b, diniUpperRight V s ≤ (M : EReal) := by
    intro a b ha _
    refine ⟨|lam1| + |lam2| + 1, by positivity, fun s hs => ?_⟩
    have hs0 : 0 ≤ s := ha.trans hs.1
    unfold diniUpperRight
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    rw [EReal.coe_le_coe_iff, div_le_iff₀ hh']
    have i1 := inc1 s (s + h) hs0 (by linarith)
    have i2 := inc2 s (s + h) hs0 (by linarith)
    have ha := hTa s (s + h) hs0 (by linarith)
    have hb := hTs s (s + h) hs0 (by linarith)
    have hd : 0 ≤ (Ta (s + h) - Ta s) / m1 := div_nonneg ha.1 hm1.le
    have he : 0 ≤ (Ts (s + h) - Ts s) / m2 := div_nonneg hb.1 hm2.le
    simp only [add_sub_cancel_left] at i1 i2
    simp only [hV]
    have q1 : lam1 * h ≤ |lam1| * h := mul_le_mul_of_nonneg_right (le_abs_self _) hh'.le
    have q2 : lam2 * h ≤ |lam2| * h := mul_le_mul_of_nonneg_right (le_abs_self _) hh'.le
    have q3 : 0 ≤ |lam1| * h := mul_nonneg (abs_nonneg _) hh'.le
    have q4 : 0 ≤ |lam2| * h := mul_nonneg (abs_nonneg _) hh'.le
    have hmax : max (Z1 (s + h)) (Z2 (s + h)) ≤ max (Z1 s) (Z2 s) + (|lam1| * h + |lam2| * h) := by
      refine max_le ?_ ?_
      · have := le_max_left (Z1 s) (Z2 s); linarith
      · have := le_max_right (Z1 s) (Z2 s); linarith
    have : (|lam1| + |lam2| + 1) * h = |lam1| * h + |lam2| * h + h := by ring
    rw [this]
    linarith
  -- a.e. drift
  have hae1 := hlip1.ae_differentiableWithinAt_of_mem (μ := volume)
  have hae2 := hlip2.ae_differentiableWithinAt_of_mem (μ := volume)
  have haeV := hlipV.ae_differentiableWithinAt_of_mem (μ := volume)
  have hne0 : ∀ᵐ s : ℝ, s ≠ 0 := by
    have : ({0} : Set ℝ)ᶜ ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.mpr (measure_singleton 0)
    filter_upwards [this] with s hs using hs
  have hdrift : ∀ᵐ s, 0 ≤ s → 0 < V s → diniUpperRight V s ≤ ((-η : ℝ) : EReal) := by
    filter_upwards [hae1, hae2, haeV, hne0] with s d1 d2 dV hsne hs hVs
    have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hsne)
    have hnhd : Ici (0 : ℝ) ∈ 𝓝 s := Ici_mem_nhds hspos
    have D1 := ((d1 hs).differentiableAt hnhd).hasDerivAt
    have D2 := ((d2 hs).differentiableAt hnhd).hasDerivAt
    have DV := ((dV hs).differentiableAt hnhd).hasDerivAt
    rw [dec_dini_of_hasDerivAt V _ s DV, EReal.coe_le_coe_iff]
    set a1 := deriv Z1 s
    set a2 := deriv Z2 s
    set aV := deriv V s
    have hnn1 : ∀ᶠ u in 𝓝 s, 0 ≤ Z1 u := (lt_mem_nhds hspos).mono fun u hu => (hnn u hu.le).1
    have hnn2 : ∀ᶠ u in 𝓝 s, 0 ≤ Z2 u := (lt_mem_nhds hspos).mono fun u hu => (hnn u hu.le).2
    -- if V = Z1 at s then aV = a1
    have hV1 : V s = Z1 s → aV = a1 := by
      intro he
      have hmin : IsLocalMin (fun u => V u - Z1 u) s :=
        Eventually.of_forall fun u => by
          show V s - Z1 s ≤ V u - Z1 u
          rw [he, sub_self]; exact sub_nonneg.mpr (le_max_left (Z1 u) (Z2 u))
      have := hmin.hasDerivAt_eq_zero (DV.sub D1)
      linarith
    have hV2 : V s = Z2 s → aV = a2 := by
      intro he
      have hmin : IsLocalMin (fun u => V u - Z2 u) s :=
        Eventually.of_forall fun u => by
          show V s - Z2 s ≤ V u - Z2 u
          rw [he, sub_self]; exact sub_nonneg.mpr (le_max_right (Z1 u) (Z2 u))
      have := hmin.hasDerivAt_eq_zero (DV.sub D2)
      linarith
    have hz1 : Z1 s = 0 → a1 = 0 := fun h0 => by
      have hmin : IsLocalMin Z1 s := hnn1.mono fun u hu => by rw [h0]; exact hu
      exact hmin.hasDerivAt_eq_zero D1
    have hz2 : Z2 s = 0 → a2 = 0 := fun h0 => by
      have hmin : IsLocalMin Z2 s := hnn2.mono fun u hu => by rw [h0]; exact hu
      exact hmin.hasDerivAt_eq_zero D2
    have hZ1s := (hnn s hs).1
    have hZ2s := (hnn s hs).2
    rcases lt_trichotomy (Z1 s) (Z2 s) with hlt | heq | hgt
    · have hVe : V s = Z2 s := max_eq_right hlt.le
      rw [hV2 hVe]
      have hd := hd8 s hspos hlt a1 a2 D1 D2
      rcases hZ1s.lt_or_eq with hp | hz
      · have := hd9 s hspos hp (hp.trans hlt) a1 D1
        linarith
      · have := hz1 hz.symm
        linarith
    · have hVe : V s = Z1 s := max_eq_left heq.ge
      rw [hV1 hVe]
      have hp1 : 0 < Z1 s := by
        have : V s = Z1 s := hVe
        linarith
      have := hd9 s hspos hp1 (heq ▸ hp1) a1 D1
      linarith
    · have hVe : V s = Z1 s := max_eq_left hgt.le
      rw [hV1 hVe]
      have hd := hd7 s hspos hgt a1 a2 D1 D2
      rcases hZ2s.lt_or_eq with hp | hz
      · have := hd9 s hspos (hp.trans hgt) hp a1 D1
        linarith
      · have := hz2 hz.symm
        linarith
  have hV0 : 0 ≤ V 0 := hVnn 0 le_rfl
  have hZ0 := hnn 0 le_rfl
  have hthr : V 0 / η ≤ t := by
    have : V 0 ≤ Z1 0 + Z2 0 := max_le (by linarith [hZ0.2]) (by linarith [hZ0.1])
    calc V 0 / η ≤ (Z1 0 + Z2 0) / η := div_le_div_of_nonneg_right this hηpos.le
      _ = 1 / η * (Z1 0 + Z2 0) := by ring
      _ ≤ t := ht
  have hVt := dec_main V hVnn hVcont hbound η hηpos hdrift t hthr
  have ht0 : 0 ≤ t := le_trans (div_nonneg hV0 hηpos.le) hthr
  have a := hnn t ht0
  have b1 : Z1 t ≤ V t := le_max_left _ _
  have b2 : Z2 t ≤ V t := le_max_right _ _
  exact ⟨by linarith [a.1], by linarith [a.2]⟩


