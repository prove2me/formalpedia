-- Prove2me | solution 1 for ProcessingNetworks.LyapunovCriteria.dini_extinction_criterion
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:51:46.477494+00:00
-- url     : https://prove2.me/submissions/49f98969-48c4-4176-9a0c-3914c6d1dcfc

import Mathlib
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative

open MeasureTheory Filter Topology Set

namespace ProcessingNetworks.LyapunovCriteria

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

end ProcessingNetworks.LyapunovCriteria

open ProcessingNetworks.LyapunovCriteria in
theorem solution
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


