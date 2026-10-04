-- Prove2me | solution 1 for ProcessingNetworks.PacketNetworks.back_pressure_fluid_model_stable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:39:16.984017+00:00
-- url     : https://prove2.me/submissions/a8d80771-62b6-4723-b80d-e8543e4128b3

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_BPFluidModel

open MeasureTheory Filter Topology Set

namespace ProcessingNetworks.PacketNetworks.BPS

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


theorem bps_lip (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
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

theorem bps_nrm_eq {I : ℕ} (v : Fin I → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin I))‖ = Real.sqrt (∑ i, v i ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [sq_abs]

theorem bps_nrm_le_sum {I : ℕ} (v : Fin I → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin I))‖ ≤ ∑ i, |v i| := by
  rw [bps_nrm_eq]
  calc Real.sqrt (∑ i, v i ^ 2) = Real.sqrt (∑ i, |v i| ^ 2) := by simp [sq_abs]
    _ ≤ Real.sqrt ((∑ i, |v i|) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg _)
    _ = ∑ i, |v i| := Real.sqrt_sq (Finset.sum_nonneg fun i _ => abs_nonneg _)

end ProcessingNetworks.PacketNetworks.BPS

open ProcessingNetworks.PacketNetworks ProcessingNetworks.PacketNetworks.BPS in
theorem solution
    {I J : ℕ} (dat : PacketNetworkData I J) (S : Finset (Fin J → ℕ)) (lam : Fin I → ℝ)
    (hload : ∃ shat ∈ hullFinset S, ∀ i, lam i < (R dat).mulVec shat i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (Dh : ℝ → Fin J → ℝ) (Th : ℝ → (Fin J → ℕ) → ℝ) (Zh : ℝ → Fin I → ℝ),
      IsBackPressureFluidModelSolution dat S lam Dh Th Zh →
      ∀ t : ℝ, δ ≤ t → Zh t = fun _ => 0 := by
  obtain ⟨shat, hshat, hlt⟩ := hload
  obtain ⟨η, hη, hηle⟩ : ∃ η : ℝ, 0 < η ∧ ∀ i, lam i + η ≤ (R dat).mulVec shat i := by
    rcases Nat.eq_zero_or_pos I with rfl | hI
    · exact ⟨1, one_pos, fun i => i.elim0⟩
    · have hne : (Finset.univ : Finset (Fin I)).Nonempty := ⟨⟨0, hI⟩, Finset.mem_univ _⟩
      refine ⟨Finset.univ.inf' hne (fun i => (R dat).mulVec shat i - lam i), ?_, fun i => ?_⟩
      · rw [Finset.lt_inf'_iff]; intro i _; linarith [hlt i]
      · have := Finset.inf'_le (fun i => (R dat).mulVec shat i - lam i) (Finset.mem_univ i)
        linarith
  refine ⟨1 / η, by positivity, fun Dh Th Zh hsol t ht => ?_⟩
  obtain ⟨⟨hZ, hZ0sum, hZnn, hD, -, -, Kc, hKc⟩, hBP⟩ := hsol
  set K := |Kc| with hK
  have hT : ∀ σ ∈ S, ∀ s u, 0 ≤ s → s ≤ u → |Th u σ - Th s σ| ≤ K * (u - s) :=
    fun σ hσ s u hs hsu =>
      (hKc σ hσ s u hs hsu).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
  set KD : ℝ := K * ∑ σ ∈ S, ∑ j, (σ j : ℝ) with hKD
  have hKD0 : 0 ≤ KD :=
    mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun j _ => Nat.cast_nonneg _)
  have hDinc : ∀ j s u, 0 ≤ s → s ≤ u → |Dh u j - Dh s j| ≤ KD * (u - s) := by
    intro j s u hs hsu
    rw [hD u (hs.trans hsu) j, hD s hs j, ← Finset.sum_sub_distrib]
    calc |∑ σ ∈ S, ((σ j : ℝ) * Th u σ - (σ j : ℝ) * Th s σ)|
        ≤ ∑ σ ∈ S, |(σ j : ℝ) * Th u σ - (σ j : ℝ) * Th s σ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ σ ∈ S, (σ j : ℝ) * (K * (u - s)) := Finset.sum_le_sum fun σ hσ => by
          rw [← mul_sub, abs_mul, Nat.abs_cast]
          exact mul_le_mul_of_nonneg_left (hT σ hσ s u hs hsu) (Nat.cast_nonneg _)
      _ ≤ ∑ σ ∈ S, (∑ j', (σ j' : ℝ)) * (K * (u - s)) := Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_right
            (Finset.single_le_sum (fun j' _ => Nat.cast_nonneg (σ j')) (Finset.mem_univ j))
            (mul_nonneg (abs_nonneg _) (by linarith))
      _ = KD * (u - s) := by rw [← Finset.sum_mul, hKD]; ring
  have hZinc : ∀ i s u, 0 ≤ s → s ≤ u →
      |Zh u i - Zh s i| ≤ (|lam i| + ∑ j, |R dat i j| * KD) * (u - s) := by
    intro i s u hs hsu
    have e : Zh u i - Zh s i = lam i * (u - s) - ∑ j, R dat i j * (Dh u j - Dh s j) := by
      rw [hZ u (hs.trans hsu) i, hZ s hs i]
      simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [e]
    have hw : 0 ≤ u - s := by linarith
    calc |lam i * (u - s) - ∑ j, R dat i j * (Dh u j - Dh s j)|
        ≤ |lam i * (u - s)| + |∑ j, R dat i j * (Dh u j - Dh s j)| := abs_sub _ _
      _ ≤ |lam i| * (u - s) + ∑ j, |R dat i j| * (KD * (u - s)) := by
          refine add_le_add (by rw [abs_mul, abs_of_nonneg hw]) ?_
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hDinc j s u hs hsu) (abs_nonneg _)
      _ = (|lam i| + ∑ j, |R dat i j| * KD) * (u - s) := by
          rw [add_mul, Finset.sum_mul]
          congr 1
          exact Finset.sum_congr rfl fun j _ => by ring
  have hLZ : ∀ i, 0 ≤ |lam i| + ∑ j, |R dat i j| * KD := fun i =>
    add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) hKD0)
  set KZ : ℝ := ∑ i, (|lam i| + ∑ j, |R dat i j| * KD) with hKZ
  have hKZ0 : 0 ≤ KZ := Finset.sum_nonneg fun i _ => hLZ i
  set f : ℝ → ℝ := fun s => ‖(WithLp.toLp 2 (Zh s) : EuclideanSpace ℝ (Fin I))‖ with hf
  have hfinc : ∀ s u, 0 ≤ s → s ≤ u → |f u - f s| ≤ KZ * (u - s) := by
    intro s u hs hsu
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← WithLp.toLp_sub]
    refine (bps_nrm_le_sum _).trans ?_
    rw [hKZ, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => by simpa using hZinc i s u hs hsu
  have hflip := bps_lip f KZ hKZ0 hfinc
  have hfnn : ∀ s, 0 ≤ s → 0 ≤ f s := fun s _ => norm_nonneg _
  have hfcont : ContinuousOn f (Ioi 0) := hflip.continuousOn.mono Ioi_subset_Ici_self
  have hbound : ∀ a b : ℝ, 0 ≤ a → a < b → ∃ M : ℝ, 0 < M ∧
      ∀ s ∈ Set.Ico a b, diniUpperRight f s ≤ (M : EReal) := by
    intro a b ha _
    refine ⟨KZ + 1, by linarith, fun s hs => ?_⟩
    have hs0 : 0 ≤ s := ha.trans hs.1
    unfold diniUpperRight
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    rw [EReal.coe_le_coe_iff, div_le_iff₀ hh']
    have h1 := hfinc s (s + h) hs0 (by linarith)
    rw [add_sub_cancel_left] at h1
    have h2 := (le_abs_self _).trans h1
    nlinarith
  -- almost-everywhere differentiability
  have haeZ : ∀ᵐ s, ∀ i, s ∈ Ici (0 : ℝ) → DifferentiableWithinAt ℝ (fun u => Zh u i) (Ici 0) s := by
    rw [ae_all_iff]
    intro i
    exact (bps_lip _ _ (hLZ i) (hZinc i)).ae_differentiableWithinAt_of_mem
  have haeD : ∀ᵐ s, ∀ j, s ∈ Ici (0 : ℝ) → DifferentiableWithinAt ℝ (fun u => Dh u j) (Ici 0) s := by
    rw [ae_all_iff]
    intro j
    exact (bps_lip _ _ hKD0 (hDinc j)).ae_differentiableWithinAt_of_mem
  have haeT : ∀ᵐ s, ∀ σ ∈ S, s ∈ Ici (0 : ℝ) →
      DifferentiableWithinAt ℝ (fun u => Th u σ) (Ici 0) s :=
    (Filter.eventually_all_finset S).mpr fun σ hσ =>
      (bps_lip _ _ (abs_nonneg Kc) (hT σ hσ)).ae_differentiableWithinAt_of_mem
  have hne0 : ∀ᵐ s : ℝ, s ≠ 0 := by
    have : ({0} : Set ℝ)ᶜ ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.mpr (measure_singleton 0)
    filter_upwards [this] with s hs using hs
  have hdrift : ∀ᵐ s, 0 ≤ s → 0 < f s → diniUpperRight f s ≤ ((-η : ℝ) : EReal) := by
    filter_upwards [haeZ, haeD, haeT, hne0] with s dZ dD dT hsne hs hfs
    have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hsne)
    have hnhd : Ici (0 : ℝ) ∈ 𝓝 s := Ici_mem_nhds hspos
    have dZv : DifferentiableWithinAt ℝ Zh (Ici 0) s := differentiableWithinAt_pi.mpr fun i => dZ i hs
    have dDv : DifferentiableWithinAt ℝ Dh (Ici 0) s := differentiableWithinAt_pi.mpr fun j => dD j hs
    have hreg : RegularPoint S Dh Th Zh s := ⟨dDv, fun σ hσ => dT σ hσ hs, dZv⟩
    set d := derivWithin Dh (Ici 0) s with hd
    have hDd : HasDerivWithinAt Dh d (Ici 0) s := dDv.hasDerivWithinAt
    obtain ⟨s1, -, hmax, heq⟩ := hBP s hs hreg d hDd
    have hDat : HasDerivAt Dh d s := hDd.hasDerivAt hnhd
    have hDj : ∀ j, HasDerivAt (fun u => Dh u j) (d j) s := fun j => (hasDerivAt_pi.mp hDat) j
    set z' : Fin I → ℝ := fun i => lam i - ∑ j, R dat i j * d j with hz'
    have hZi : ∀ i, HasDerivAt (fun u => Zh u i) (z' i) s := by
      intro i
      have hl : HasDerivAt (fun u => Zh 0 i + lam i * u) (lam i) s := by
        simpa using ((hasDerivAt_id s).const_mul (lam i)).const_add (Zh 0 i)
      have hsum : HasDerivAt (fun u => ∑ j, R dat i j * Dh u j) (∑ j, R dat i j * d j) s :=
        HasDerivAt.fun_sum fun j _ => (hDj j).const_mul _
      refine (hl.sub hsum).congr_of_eventuallyEq ?_
      filter_upwards [lt_mem_nhds hspos] with u hu
      rw [hZ u hu.le i]
      simp [Matrix.mulVec, dotProduct]
    set V : ℝ → ℝ := fun u => ∑ i, Zh u i ^ 2 with hV
    have hfV : ∀ u, f u = Real.sqrt (V u) := fun u => by simp only [hf, hV, bps_nrm_eq]
    have hVd : HasDerivAt V (∑ i, 2 * Zh s i * z' i) s := by
      refine (HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin I)))
        fun i _ => (hZi i).pow 2).congr_deriv ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      simp
    have hVpos : V s ≠ 0 := by
      have : 0 < Real.sqrt (V s) := by rw [← hfV]; exact hfs
      exact (Real.sqrt_pos.mp this).ne'
    have hfd : HasDerivAt f ((∑ i, 2 * Zh s i * z' i) / (2 * Real.sqrt (V s))) s :=
      (hVd.sqrt hVpos).congr_of_eventuallyEq (Eventually.of_forall fun u => hfV u)
    rw [dec_dini_of_hasDerivAt f _ s hfd, EReal.coe_le_coe_iff]
    have hdot : ∑ i, Zh s i * z' i ≤ -η * ∑ i, Zh s i := by
      have h1 := hmax shat hshat
      have h2 : ∑ i, Zh s i * z' i = ∑ i, Zh s i * lam i - Zh s ⬝ᵥ (R dat).mulVec d := by
        simp only [hz', dotProduct, Matrix.mulVec, mul_sub, Finset.sum_sub_distrib]
      have h3 : ∑ i, Zh s i * lam i - Zh s ⬝ᵥ (R dat).mulVec shat ≤ -η * ∑ i, Zh s i := by
        rw [dotProduct, ← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        nlinarith [hZnn s hs i, hηle i]
      linarith
    have hsumZ : f s ≤ ∑ i, Zh s i :=
      (bps_nrm_le_sum _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => abs_of_nonneg (hZnn s hs i)))
    rw [← hfV s, div_le_iff₀ (by positivity)]
    have e2 : ∑ i, 2 * Zh s i * z' i = 2 * ∑ i, Zh s i * z' i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e2]
    nlinarith [mul_le_mul_of_nonneg_left hsumZ hη.le]
  have hf0 : f 0 ≤ 1 := by
    calc f 0 ≤ ∑ i, |Zh 0 i| := bps_nrm_le_sum _
      _ = ∑ i, Zh 0 i := Finset.sum_congr rfl fun i _ => abs_of_nonneg (hZnn 0 le_rfl i)
      _ = 1 := hZ0sum
  have hthr : f 0 / η ≤ t := le_trans (div_le_div_of_nonneg_right hf0 hη.le) ht
  have hft := dec_main f hfnn hfcont hbound η hη hdrift t hthr
  have h0 : (WithLp.toLp 2 (Zh t) : EuclideanSpace ℝ (Fin I)) = 0 := norm_eq_zero.mp hft
  funext i
  have := congrArg (fun v : EuclideanSpace ℝ (Fin I) => v i) h0
  simpa using this


