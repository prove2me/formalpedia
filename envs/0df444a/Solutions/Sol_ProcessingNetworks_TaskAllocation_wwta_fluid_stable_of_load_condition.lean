-- Prove2me | solution 1 for ProcessingNetworks.TaskAllocation.wwta_fluid_stable_of_load_condition
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:42:21.939502+00:00
-- url     : https://prove2.me/submissions/67becd66-66e2-4c26-807c-6c6d21284b26

import Mathlib
import Definitions.Def_ProcessingNetworks_TaskAllocation_TaskAllocationModel
import Definitions.Def_ProcessingNetworks_TaskAllocation_FluidModel

open MeasureTheory Filter Topology Set

namespace ProcessingNetworks.TaskAllocation.WW


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

end ProcessingNetworks.TaskAllocation.WW

open ProcessingNetworks.TaskAllocation ProcessingNetworks.TaskAllocation.WW in
theorem solution
    {L K : ℕ} [Nonempty (Fin K)] (dat : TaskAllocationData L K)
    (hload : ∃ lam : Fin L → Fin K → ℝ, (∀ ℓ k, 0 ≤ lam ℓ k) ∧
      (∀ ℓ, ∑ k, lam ℓ k = dat.nu ℓ) ∧ (∀ k, ∑ ℓ, dat.m ℓ k * lam ℓ k < 1)) :
    WWTAFluidStable dat := by
  obtain ⟨lam, hlam0, hlamsum, hρ⟩ := hload
  obtain ⟨η, hη, hηle⟩ : ∃ η : ℝ, 0 < η ∧ ∀ k, ∑ ℓ, dat.m ℓ k * lam ℓ k + η ≤ 1 := by
    have hne : (Finset.univ : Finset (Fin K)).Nonempty := Finset.univ_nonempty
    refine ⟨Finset.univ.inf' hne (fun k => 1 - ∑ ℓ, dat.m ℓ k * lam ℓ k), ?_, fun k => ?_⟩
    · rw [Finset.lt_inf'_iff]; intro k _; linarith [hρ k]
    · have := Finset.inf'_le (fun k => 1 - ∑ ℓ, dat.m ℓ k * lam ℓ k) (Finset.mem_univ k)
      linarith
  set Msum : ℝ := ∑ ℓ, ∑ k, dat.m ℓ k with hMsum
  have hMsum0 : 0 ≤ Msum := Finset.sum_nonneg fun ℓ _ => Finset.sum_nonneg fun k _ => (dat.hm ℓ k).le
  refine ⟨(Msum + 1) / η, by positivity, fun Eh Dh Wh Zh hsol t ht => ?_⟩
  obtain ⟨⟨hZ, hZnn, ⟨-, -, Kc, hKc⟩, -, hW, hdep⟩, hww⟩ := hsol
  set Kk := |Kc| with hKk
  have hE : ∀ ℓ k s u, 0 ≤ s → s ≤ u → |Eh u ℓ k - Eh s ℓ k| ≤ Kk * (u - s) := fun ℓ k s u hs hsu =>
    ((hKc s u hs hsu ℓ k).1).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
  have hD : ∀ ℓ k s u, 0 ≤ s → s ≤ u → |Dh u ℓ k - Dh s ℓ k| ≤ Kk * (u - s) := fun ℓ k s u hs hsu =>
    ((hKc s u hs hsu ℓ k).2).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
  have hKk0 : 0 ≤ Kk := abs_nonneg _
  -- workload increments
  set LW : Fin K → ℝ := fun k => ∑ ℓ, dat.m ℓ k * (2 * Kk) with hLW
  have hLW0 : ∀ k, 0 ≤ LW k := fun k =>
    Finset.sum_nonneg fun ℓ _ => mul_nonneg (dat.hm ℓ k).le (by positivity)
  have hWinc : ∀ k s u, 0 ≤ s → s ≤ u → |Wh u k - Wh s k| ≤ LW k * (u - s) := by
    intro k s u hs hsu
    have e : Wh u k - Wh s k =
        ∑ ℓ, dat.m ℓ k * ((Eh u ℓ k - Eh s ℓ k) - (Dh u ℓ k - Dh s ℓ k)) := by
      rw [hW u (hs.trans hsu) k, hW s hs k, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [hZ u (hs.trans hsu) ℓ k, hZ s hs ℓ k]; ring
    rw [e, hLW, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ℓ _ => ?_)
    rw [abs_mul, abs_of_pos (dat.hm ℓ k), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (dat.hm ℓ k).le
    have h1 := hE ℓ k s u hs hsu
    have h2 := hD ℓ k s u hs hsu
    calc |(Eh u ℓ k - Eh s ℓ k) - (Dh u ℓ k - Dh s ℓ k)|
        ≤ |Eh u ℓ k - Eh s ℓ k| + |Dh u ℓ k - Dh s ℓ k| := abs_sub _ _
      _ ≤ 2 * Kk * (u - s) := by linarith
  set KW : ℝ := ∑ k, LW k with hKW
  have hKW0 : 0 ≤ KW := Finset.sum_nonneg fun k _ => hLW0 k
  have hWnn : ∀ s, 0 ≤ s → ∀ k, 0 ≤ Wh s k := fun s hs k => by
    rw [hW s hs k]
    exact Finset.sum_nonneg fun ℓ _ => mul_nonneg (dat.hm ℓ k).le (hZnn s hs ℓ k)
  set f : ℝ → ℝ := fun s => ‖(WithLp.toLp 2 (Wh s) : EuclideanSpace ℝ (Fin K))‖ with hf
  have hfinc : ∀ s u, 0 ≤ s → s ≤ u → |f u - f s| ≤ KW * (u - s) := by
    intro s u hs hsu
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← WithLp.toLp_sub]
    refine (bps_nrm_le_sum _).trans ?_
    rw [hKW, Finset.sum_mul]
    exact Finset.sum_le_sum fun k _ => by simpa using hWinc k s u hs hsu
  have hflip := bps_lip f KW hKW0 hfinc
  have hfnn : ∀ s, 0 ≤ s → 0 ≤ f s := fun s _ => norm_nonneg _
  have hfcont : ContinuousOn f (Ioi 0) := hflip.continuousOn.mono Ioi_subset_Ici_self
  have hbound : ∀ a b : ℝ, 0 ≤ a → a < b → ∃ M : ℝ, 0 < M ∧
      ∀ s ∈ Set.Ico a b, diniUpperRight f s ≤ (M : EReal) := by
    intro a b ha _
    refine ⟨KW + 1, by linarith, fun s hs => ?_⟩
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
  have haeE : ∀ᵐ s, ∀ ℓ k, s ∈ Ici (0 : ℝ) →
      DifferentiableWithinAt ℝ (fun u => Eh u ℓ k) (Ici 0) s := by
    rw [ae_all_iff]; intro ℓ; rw [ae_all_iff]; intro k
    exact (bps_lip _ _ hKk0 (hE ℓ k)).ae_differentiableWithinAt_of_mem
  have haeD : ∀ᵐ s, ∀ ℓ k, s ∈ Ici (0 : ℝ) →
      DifferentiableWithinAt ℝ (fun u => Dh u ℓ k) (Ici 0) s := by
    rw [ae_all_iff]; intro ℓ; rw [ae_all_iff]; intro k
    exact (bps_lip _ _ hKk0 (hD ℓ k)).ae_differentiableWithinAt_of_mem
  have hne0 : ∀ᵐ s : ℝ, s ≠ 0 := by
    have : ({0} : Set ℝ)ᶜ ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.mpr (measure_singleton 0)
    filter_upwards [this] with s hs using hs
  have hdrift : ∀ᵐ s, 0 ≤ s → 0 < f s → diniUpperRight f s ≤ ((-η : ℝ) : EReal) := by
    filter_upwards [haeE, haeD, hne0] with s dE dD hsne hs hfs
    have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hsne)
    have hnhd : Ici (0 : ℝ) ∈ 𝓝 s := Ici_mem_nhds hspos
    set e : Fin L → Fin K → ℝ := fun ℓ k => deriv (fun u => Eh u ℓ k) s with he
    set dd : Fin L → Fin K → ℝ := fun ℓ k => deriv (fun u => Dh u ℓ k) s with hdd
    have hEd : ∀ ℓ k, HasDerivAt (fun u => Eh u ℓ k) (e ℓ k) s := fun ℓ k =>
      ((dE ℓ k hs).differentiableAt hnhd).hasDerivAt
    have hDd : ∀ ℓ k, HasDerivAt (fun u => Dh u ℓ k) (dd ℓ k) s := fun ℓ k =>
      ((dD ℓ k hs).differentiableAt hnhd).hasDerivAt
    set w' : Fin K → ℝ := fun k => ∑ ℓ, dat.m ℓ k * (e ℓ k - dd ℓ k) with hw'
    have hWd : ∀ k, HasDerivAt (fun u => Wh u k) (w' k) s := by
      intro k
      have hsum : HasDerivAt (fun u => ∑ ℓ, dat.m ℓ k * (Zh 0 ℓ k + Eh u ℓ k - Dh u ℓ k))
          (w' k) s := by
        refine HasDerivAt.fun_sum fun ℓ _ => ?_
        have := (((hEd ℓ k).const_add (Zh 0 ℓ k)).sub (hDd ℓ k)).const_mul (dat.m ℓ k)
        exact this
      refine hsum.congr_of_eventuallyEq ?_
      filter_upwards [lt_mem_nhds hspos] with u hu
      rw [hW u hu.le k]
      exact Finset.sum_congr rfl fun ℓ _ => by rw [hZ u hu.le ℓ k]
    set V : ℝ → ℝ := fun u => ∑ k, Wh u k ^ 2 with hV
    have hfV : ∀ u, f u = Real.sqrt (V u) := fun u => by simp only [hf, hV, bps_nrm_eq]
    have hVd : HasDerivAt V (∑ k, 2 * Wh s k * w' k) s := by
      refine (HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin K)))
        fun k _ => (hWd k).pow 2).congr_deriv ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      simp
    have hVpos : V s ≠ 0 := by
      have : 0 < Real.sqrt (V s) := by rw [← hfV]; exact hfs
      exact (Real.sqrt_pos.mp this).ne'
    have hfd : HasDerivAt f ((∑ k, 2 * Wh s k * w' k) / (2 * Real.sqrt (V s))) s :=
      (hVd.sqrt hVpos).congr_of_eventuallyEq (Eventually.of_forall fun u => hfV u)
    rw [dec_dini_of_hasDerivAt f _ s hfd, EReal.coe_le_coe_iff]
    -- the key drift inequality
    have hdep' : ∀ k, Wh s k * ∑ ℓ, dat.m ℓ k * dd ℓ k = Wh s k := by
      intro k
      rcases (hWnn s hs k).lt_or_eq with hpos | hzero
      · rw [hdep s hspos k hpos (fun ℓ => dd ℓ k) (fun ℓ => hDd ℓ k), mul_one]
      · rw [← hzero, zero_mul]
    have hwwta : ∀ ℓ, ∑ k, dat.m ℓ k * Wh s k * e ℓ k ≤ ∑ k, lam ℓ k * (dat.m ℓ k * Wh s k) := by
      intro ℓ
      rw [hww s hspos ℓ (fun k => e ℓ k) (fun k => hEd ℓ k), ← hlamsum ℓ, Finset.sum_mul]
      refine Finset.sum_le_sum fun k _ => ?_
      exact mul_le_mul_of_nonneg_left
        (ciInf_le (Finite.bddBelow_range _) k) (hlam0 ℓ k)
    have hdot : ∑ k, Wh s k * w' k ≤ -η * ∑ k, Wh s k := by
      have e1 : ∑ k, Wh s k * w' k =
          ∑ ℓ, ∑ k, dat.m ℓ k * Wh s k * e ℓ k - ∑ k, Wh s k * ∑ ℓ, dat.m ℓ k * dd ℓ k := by
        rw [Finset.sum_comm (f := fun ℓ k => dat.m ℓ k * Wh s k * e ℓ k), ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hw', mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
        congr 1
        exact Finset.sum_congr rfl fun ℓ _ => by ring
      have e2 : ∑ k, Wh s k * ∑ ℓ, dat.m ℓ k * dd ℓ k = ∑ k, Wh s k :=
        Finset.sum_congr rfl fun k _ => hdep' k
      have e3 : ∑ ℓ, ∑ k, lam ℓ k * (dat.m ℓ k * Wh s k) =
          ∑ k, (∑ ℓ, dat.m ℓ k * lam ℓ k) * Wh s k := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun ℓ _ => by ring
      have h4 : ∑ k, (∑ ℓ, dat.m ℓ k * lam ℓ k) * Wh s k - ∑ k, Wh s k ≤ -η * ∑ k, Wh s k := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_le_sum fun k _ => ?_
        nlinarith [hWnn s hs k, hηle k]
      have h5 := Finset.sum_le_sum fun ℓ (_ : ℓ ∈ Finset.univ) => hwwta ℓ
      rw [e1, e2]
      linarith
    have hsumW : f s ≤ ∑ k, Wh s k :=
      (bps_nrm_le_sum _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => abs_of_nonneg (hWnn s hs k)))
    rw [← hfV s, div_le_iff₀ (by positivity)]
    have e2 : ∑ k, 2 * Wh s k * w' k = 2 * ∑ k, Wh s k * w' k := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [e2]
    nlinarith [mul_le_mul_of_nonneg_left hsumW hη.le]
  -- initial value and conclusion
  have hZ0nn : 0 ≤ ∑ ℓ, ∑ k, Zh 0 ℓ k :=
    Finset.sum_nonneg fun ℓ _ => Finset.sum_nonneg fun k _ => hZnn 0 le_rfl ℓ k
  have hf0 : f 0 ≤ Msum * ∑ ℓ, ∑ k, Zh 0 ℓ k := by
    calc f 0 ≤ ∑ k, |Wh 0 k| := bps_nrm_le_sum _
      _ = ∑ k, ∑ ℓ, dat.m ℓ k * Zh 0 ℓ k := Finset.sum_congr rfl fun k _ => by
          rw [abs_of_nonneg (hWnn 0 le_rfl k), hW 0 le_rfl k]
      _ = ∑ ℓ, ∑ k, dat.m ℓ k * Zh 0 ℓ k := Finset.sum_comm
      _ ≤ ∑ ℓ, ∑ k, Msum * Zh 0 ℓ k := Finset.sum_le_sum fun ℓ _ => Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right
            ((Finset.single_le_sum (fun k' _ => (dat.hm ℓ k').le) (Finset.mem_univ k)).trans
              (Finset.single_le_sum (f := fun ℓ' => ∑ k', dat.m ℓ' k')
                (fun ℓ' _ => Finset.sum_nonneg fun k' _ => (dat.hm ℓ' k').le) (Finset.mem_univ ℓ)))
            (hZnn 0 le_rfl ℓ k)
      _ = Msum * ∑ ℓ, ∑ k, Zh 0 ℓ k := by simp only [Finset.mul_sum]
  have hthr : f 0 / η ≤ t := by
    refine le_trans ?_ ht
    rw [show (Msum + 1) / η * ∑ ℓ, ∑ k, Zh 0 ℓ k = ((Msum + 1) * ∑ ℓ, ∑ k, Zh 0 ℓ k) / η by ring]
    exact div_le_div_of_nonneg_right (by nlinarith) hη.le
  have hft := dec_main f hfnn hfcont hbound η hη hdrift t hthr
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  have h0 : (WithLp.toLp 2 (Wh t) : EuclideanSpace ℝ (Fin K)) = 0 := norm_eq_zero.mp hft
  have hWt : ∀ k, Wh t k = 0 := fun k => by
    have := congrArg (fun v : EuclideanSpace ℝ (Fin K) => v k) h0
    simpa using this
  funext ℓ k
  have hsum0 := hWt k
  rw [hW t ht0 k] at hsum0
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun ℓ' _ =>
    mul_nonneg (dat.hm ℓ' k).le (hZnn t ht0 ℓ' k)).mp hsum0 ℓ (Finset.mem_univ ℓ)
  rcases mul_eq_zero.mp hterm with h | h
  · exact absurd h (dat.hm ℓ k).ne'
  · exact h


