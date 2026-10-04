-- Prove2me | solution 1 for ProcessingNetworks.FeedforwardStability.hlsps_fluid_model_stable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:03:33.237577+00:00
-- url     : https://prove2.me/submissions/ebe928b4-5d74-4967-87e0-713469dd86ea

import Mathlib
import Definitions.Def_ProcessingNetworks_FeedforwardStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FeedforwardStability_WorkloadOperator
import Definitions.Def_ProcessingNetworks_FeedforwardStability_HLSPS

open MeasureTheory Filter Topology Set

namespace ProcessingNetworks.FeedforwardStability.DRE

open ProcessingNetworks.FeedforwardStability

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


theorem dre_transient {I : ℕ} (P : Matrix (Fin I) (Fin I) ℝ) (hP_nonneg : ∀ i j, 0 ≤ P i j)
    (hP_transient : ∀ i j, Tendsto (fun n => (P ^ n) i j) atTop (nhds 0))
    (v : Fin I → ℝ) (hvnn : ∀ i, 0 ≤ v i) (hvsub : ∀ i, v i ≤ ∑ k, P k i * v k) :
    ∀ i, v i = 0 := by
  have hiter : ∀ n i, v i ≤ ∑ k, (P ^ n) k i * v k := by
    intro n
    induction n with
    | zero => intro i; simp [Matrix.one_apply]
    | succ n ih =>
      intro i
      calc v i ≤ ∑ k, P k i * v k := hvsub i
        _ ≤ ∑ k, P k i * ∑ l, (P ^ n) l k * v l :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (ih k) (hP_nonneg k i)
        _ = ∑ l, (P ^ (n + 1)) l i * v l := by
          rw [pow_succ]
          simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
          ring
  intro i
  have hlim : Tendsto (fun n => ∑ k, (P ^ n) k i * v k) atTop (nhds 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset (Fin I))
      (fun k _ => (hP_transient k i).mul_const (v k))
    simpa using this
  exact le_antisymm (ge_of_tendsto hlim (Eventually.of_forall fun n => hiter n i)) (hvnn i)

theorem dre_fix {I : ℕ} (P Q : Matrix (Fin I) (Fin I) ℝ) (hQ : (1 - P.transpose) * Q = 1)
    (x : Fin I → ℝ) (i : Fin I) : (Q.mulVec x) i = x i + ∑ k, P k i * (Q.mulVec x) k := by
  have h : (1 - P.transpose).mulVec (Q.mulVec x) = x := by
    rw [Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]
  have h2 := congrFun h i
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply] at h2
  have h3 : (P.transpose.mulVec (Q.mulVec x)) i = ∑ k, P k i * (Q.mulVec x) k := by
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [h3] at h2
  linarith

theorem dre_Qpos {I : ℕ} (P Q : Matrix (Fin I) (Fin I) ℝ) (hQ : (1 - P.transpose) * Q = 1)
    (hP_nonneg : ∀ i j, 0 ≤ P i j)
    (hP_transient : ∀ i j, Tendsto (fun n => (P ^ n) i j) atTop (nhds 0))
    (x : Fin I → ℝ) (hx : ∀ i, 0 ≤ x i) : ∀ i, x i ≤ (Q.mulVec x) i := by
  set y := Q.mulVec x with hy
  have hfix : ∀ i, y i = x i + ∑ k, P k i * y k := dre_fix P Q hQ x
  have hv := dre_transient P hP_nonneg hP_transient (fun i => max (-y i) 0)
    (fun i => le_max_right _ _) (fun i => by
      rcases le_or_gt 0 (y i) with h | h
      · rw [max_eq_right (by linarith)]
        exact Finset.sum_nonneg fun k _ => mul_nonneg (hP_nonneg k i) (le_max_right _ _)
      · rw [max_eq_left (by linarith), hfix i]
        have : ∑ k, P k i * (-y k) ≤ ∑ k, P k i * max (-y k) 0 :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hP_nonneg k i)
        have h2 : ∑ k, P k i * (-y k) = -∑ k, P k i * y k := by
          rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
        linarith [hx i])
  have hynn : ∀ i, 0 ≤ y i := fun i => by
    have := hv i
    by_contra hneg; push_neg at hneg
    rw [max_eq_left (by linarith)] at this; linarith
  intro i
  rw [hfix i]
  linarith [Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => mul_nonneg (hP_nonneg k i) (hynn k)]

theorem dre_core {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ)
    (hQ : IsRoutingInverse dat.P Q)
    (hm : ∀ i, 0 < dat.m i) (hb : ∀ k, 0 < dat.b k)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0))
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) (hsol : IsFluidModelSolutionQN dat Dh Fh Th Zh)
    (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ (j : Fin I) (t : ℝ), 0 < t → 0 < Zh t j →
      ∀ d : ℝ, HasDerivAt (fun s => Dh s j) d t → totalArrivalRates dat Q j + ε ≤ d) :
    ∀ t : ℝ, (∑ i, (Q.mulVec (Zh 0)) i) / ε ≤ t → Zh t = fun _ => 0 := by
  obtain ⟨hZ, hZnn, hDF, hmF, ⟨hT0, hTmono⟩, hcap⟩ := hsol
  set α := totalArrivalRates dat Q with hα
  have hαfix : ∀ i, α i = dat.lam i + ∑ k, dat.P k i * α k := dre_fix dat.P Q hQ.2 dat.lam
  -- D = T / m on [0, ∞)
  have hDT : ∀ s, 0 ≤ s → ∀ i, Dh s i = Th s i / dat.m i := by
    intro s hs i
    rw [hDF s hs i, eq_div_iff (hm i).ne', mul_comm, hmF s hs i]
  have hDinc : ∀ i s t, 0 ≤ s → s ≤ t →
      0 ≤ Dh t i - Dh s i ∧ Dh t i - Dh s i ≤ dat.b (dat.p i) / dat.m i * (t - s) := by
    intro i s t hs hst
    have ht : 0 ≤ t := hs.trans hst
    rw [hDT t ht, hDT s hs, ← sub_div]
    have hTi : 0 ≤ Th t i - Th s i := sub_nonneg.mpr (hTmono hst i)
    have hcapi := hcap s t hs hst (dat.p i)
    have hle : Th t i - Th s i ≤ ∑ l ∈ poolBuffers dat (dat.p i), (Th t l - Th s l) :=
      Finset.single_le_sum (f := fun l => Th t l - Th s l)
        (fun l _ => sub_nonneg.mpr (hTmono hst l)) (by simp [poolBuffers])
    constructor
    · exact div_nonneg hTi (hm i).le
    · rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (by linarith) (hm i).le
  have hlip : ∀ i, LipschitzOnWith (Real.toNNReal (dat.b (dat.p i) / dat.m i))
      (fun s => Dh s i) (Ici 0) := by
    intro i
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have hc : 0 ≤ dat.b (dat.p i) / dat.m i := div_nonneg (hb _).le (hm i).le
    rw [Real.coe_toNNReal _ hc, Real.dist_eq, Real.dist_eq]
    rcases le_total x y with hxy | hxy
    · have := hDinc i x y hx hxy
      rw [abs_sub_comm, abs_of_nonneg this.1, abs_sub_comm, abs_of_nonneg (by linarith)]
      exact this.2
    · have := hDinc i y x hy hxy
      rw [abs_of_nonneg this.1, abs_of_nonneg (by linarith)]
      exact this.2
  -- the Lyapunov function
  set g : ℝ → ℝ := fun s => ∑ i, (Q.mulVec (Zh s)) i with hg
  have hQZ : ∀ s, 0 ≤ s → ∀ i, (Q.mulVec (Zh s)) i = (Q.mulVec (Zh 0)) i + s * α i - Dh s i := by
    intro s hs
    have hZv : Zh s = Zh 0 + s • dat.lam - (1 - dat.P.transpose).mulVec (Dh s) := by
      ext i
      rw [hZ s hs i]
      simp [Matrix.sub_mulVec, Matrix.mulVec, dotProduct, Matrix.transpose_apply, hDF s hs]
      ring
    intro i
    rw [hZv, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      hQ.1, Matrix.one_mulVec]
    simp [hα, totalArrivalRates]
  have hgform : ∀ s, 0 ≤ s → g s = g 0 + s * ∑ i, α i - ∑ i, Dh s i := by
    intro s hs
    simp only [hg]
    rw [Finset.sum_congr rfl fun i _ => hQZ s hs i, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.mul_sum]
  have hgZ : ∀ s, 0 ≤ s → ∑ i, Zh s i ≤ g s := fun s hs =>
    Finset.sum_le_sum fun i _ => dre_Qpos dat.P Q hQ.2 hP_nonneg hP_transient (Zh s) (hZnn s hs) i
  have hgnn : ∀ s, 0 ≤ s → 0 ≤ g s := fun s hs =>
    (Finset.sum_nonneg fun i _ => hZnn s hs i).trans (hgZ s hs)
  have hDcont : ∀ i, ContinuousOn (fun s => Dh s i) (Ici 0) := fun i => (hlip i).continuousOn
  have hgcont : ContinuousOn g (Ioi 0) := by
    have : ContinuousOn (fun s => g 0 + s * ∑ i, α i - ∑ i, Dh s i) (Ioi 0) := by
      refine (continuousOn_const.add (continuousOn_id.mul continuousOn_const)).sub ?_
      exact continuousOn_finset_sum _ fun i _ => (hDcont i).mono Ioi_subset_Ici_self
    exact this.congr fun s hs => hgform s (le_of_lt hs)
  have hbound : ∀ a b : ℝ, 0 ≤ a → a < b → ∃ M : ℝ, 0 < M ∧
      ∀ t ∈ Set.Ico a b, diniUpperRight g t ≤ (M : EReal) := by
    intro a b ha _
    refine ⟨|∑ i, α i| + 1, by positivity, fun t ht => ?_⟩
    have ht0 : 0 ≤ t := ha.trans ht.1
    unfold diniUpperRight
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    rw [EReal.coe_le_coe_iff, div_le_iff₀ hh', hgform (t + h) (by linarith), hgform t ht0]
    have : 0 ≤ ∑ i, (Dh (t + h) i - Dh t i) :=
      Finset.sum_nonneg fun i _ => (hDinc i t (t + h) ht0 (by linarith)).1
    rw [Finset.sum_sub_distrib] at this
    nlinarith [le_abs_self (∑ i, α i)]
  -- a.e. drift of g
  have hae : ∀ᵐ t, ∀ i, t ∈ Ici (0 : ℝ) → DifferentiableWithinAt ℝ (fun s => Dh s i) (Ici 0) t :=
    ae_all_iff.mpr fun i => (hlip i).ae_differentiableWithinAt_of_mem
  have hne0 : ∀ᵐ t : ℝ, t ≠ 0 := by
    have : ({0} : Set ℝ)ᶜ ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.mpr (measure_singleton 0)
    filter_upwards [this] with t ht using ht
  have hgdrift : ∀ᵐ t, 0 ≤ t → 0 < g t → diniUpperRight g t ≤ ((-ε : ℝ) : EReal) := by
    filter_upwards [hae, hne0] with t hdiff htne ht hgt
    have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htne)
    have hDd : ∀ i, HasDerivAt (fun s => Dh s i) (deriv (fun s => Dh s i) t) t := fun i =>
      ((hdiff i ht).differentiableAt (Ici_mem_nhds htpos)).hasDerivAt
    set d : Fin I → ℝ := fun i => deriv (fun s => Dh s i) t with hd
    -- derivative of Z_j
    have hZd : ∀ j, HasDerivAt (fun s => Zh s j) (dat.lam j + ∑ k, dat.P k j * d k - d j) t := by
      intro j
      have h1 : HasDerivAt (fun s => Zh 0 j + dat.lam j * s + ∑ k, dat.P k j * Dh s k - Dh s j)
          (0 + dat.lam j * 1 + ∑ k, dat.P k j * d k - d j) t :=
        (((hasDerivAt_const t _).add ((hasDerivAt_id t).const_mul _)).add
          (HasDerivAt.fun_sum fun k _ => (hDd k).const_mul _)).sub (hDd j)
      rw [zero_add, mul_one] at h1
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [lt_mem_nhds htpos] with s hs
      rw [hZ s hs.le j]
      congr 2
      exact Finset.sum_congr rfl fun k _ => by rw [hDF s hs.le k]
    -- u = d - α is nonnegative
    have hv := dre_transient dat.P hP_nonneg hP_transient (fun j => max (-(d j - α j)) 0)
      (fun j => le_max_right _ _) (fun j => by
        rcases (hZnn t ht j).lt_or_eq with hpos | hzero
        · have := hdrift j t htpos hpos (d j) (hDd j)
          rw [max_eq_right (by simp only [hα] at this ⊢; linarith)]
          exact Finset.sum_nonneg fun k _ => mul_nonneg (hP_nonneg k j) (le_max_right _ _)
        · have hmin : IsLocalMin (fun s => Zh s j) t := by
            filter_upwards [lt_mem_nhds htpos] with s hs
            rw [← hzero]; exact hZnn s hs.le j
          have h0 := hmin.hasDerivAt_eq_zero (hZd j)
          have hu : -(d j - α j) = ∑ k, dat.P k j * (-(d k - α k)) := by
            rw [hαfix j]
            have : ∑ k, dat.P k j * (-(d k - α k)) = ∑ k, dat.P k j * α k - ∑ k, dat.P k j * d k := by
              rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
            rw [this]; linarith
          have hs : ∑ k, dat.P k j * (-(d k - α k)) ≤ ∑ k, dat.P k j * max (-(d k - α k)) 0 :=
            Finset.sum_le_sum fun k _ =>
              mul_le_mul_of_nonneg_left (le_max_left _ _) (hP_nonneg k j)
          have hs0 : 0 ≤ ∑ k, dat.P k j * max (-(d k - α k)) 0 :=
            Finset.sum_nonneg fun k _ => mul_nonneg (hP_nonneg k j) (le_max_right _ _)
          exact max_le (hu ▸ hs) hs0)
    have hu : ∀ j, 0 ≤ d j - α j := fun j => by
      have := hv j
      by_contra hneg; push_neg at hneg
      rw [max_eq_left (by linarith)] at this; linarith
    -- some buffer is nonempty
    obtain ⟨j0, hj0⟩ : ∃ j, 0 < Zh t j := by
      by_contra hall
      push_neg at hall
      have hz : Zh t = 0 := funext fun j => le_antisymm (hall j) (hZnn t ht j)
      have : g t = 0 := by simp [hg, hz]
      linarith
    have hj0d := hdrift j0 t htpos hj0 (d j0) (hDd j0)
    -- derivative of g
    have hgd : HasDerivAt g (∑ i, α i - ∑ i, d i) t := by
      have h1 : HasDerivAt (fun s => g 0 + s * ∑ i, α i - ∑ i, Dh s i)
          (0 + 1 * ∑ i, α i - ∑ i, d i) t :=
        ((hasDerivAt_const t _).add ((hasDerivAt_id t).mul_const _)).sub
          (HasDerivAt.fun_sum fun i _ => hDd i)
      rw [zero_add, one_mul] at h1
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [lt_mem_nhds htpos] with s hs
      exact hgform s hs.le
    rw [dec_dini_of_hasDerivAt g _ t hgd, EReal.coe_le_coe_iff]
    have hsum : ∑ i, (d i - α i) ≥ d j0 - α j0 :=
      Finset.single_le_sum (f := fun i => d i - α i) (fun i _ => hu i) (Finset.mem_univ j0)
    rw [Finset.sum_sub_distrib] at hsum
    simp only [hα] at hj0d ⊢
    linarith
  intro t ht
  have hg0 : 0 ≤ g 0 := hgnn 0 le_rfl
  have ht0 : 0 ≤ t := le_trans (div_nonneg hg0 hε.le) ht
  have hgt := dec_main g hgnn hgcont hbound ε hε hgdrift t ht
  have hsumZ : ∑ i, Zh t i = 0 := le_antisymm (hgt ▸ hgZ t ht0)
    (Finset.sum_nonneg fun i _ => hZnn t ht0 i)
  funext i
  exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hZnn t ht0 i).mp hsumZ i (Finset.mem_univ i)

end ProcessingNetworks.FeedforwardStability.DRE

open ProcessingNetworks.FeedforwardStability ProcessingNetworks.FeedforwardStability.DRE in
theorem solution
    {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ)
    (hQ : IsRoutingInverse dat.P Q)
    (hα_pos : ∀ i : Fin I, 0 < totalArrivalRates dat Q i)
    (hload : ∀ k : Fin K, workloadOperator dat Q dat.lam k < dat.b k) :
    HLSPSFluidStable dat Q := by
  rcases Nat.eq_zero_or_pos I with hI | hI
  · subst hI
    exact ⟨1, one_pos, fun _ _ _ Zh _ t _ => funext fun i => i.elim0⟩
  set α := totalArrivalRates dat Q with hα
  -- loads are positive
  have hρpos : ∀ i, 0 < workloadOperator dat Q dat.lam (dat.p i) := by
    intro i
    unfold workloadOperator
    have hmem : i ∈ poolBuffers dat (dat.p i) := by simp [poolBuffers]
    have hterm : ∀ l ∈ poolBuffers dat (dat.p i), 0 ≤ dat.m l * (Q.mulVec dat.lam) l :=
      fun l _ => mul_nonneg (dat.m_pos l).le (hα_pos l).le
    exact lt_of_lt_of_le (mul_pos (dat.m_pos i) (hα_pos i))
      (Finset.single_le_sum hterm hmem)
  have hne : (Finset.univ : Finset (Fin I)).Nonempty := ⟨⟨0, hI⟩, Finset.mem_univ _⟩
  set ε : ℝ := Finset.univ.inf' hne
    (fun i : Fin I => α i * (dat.b (dat.p i) / workloadOperator dat Q dat.lam (dat.p i) - 1))
    with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef, Finset.lt_inf'_iff]
    intro i _
    refine mul_pos (hα_pos i) (sub_pos.mpr ?_)
    rw [one_lt_div (hρpos i)]
    exact hload _
  have hεle : ∀ i, ε ≤ α i * (dat.b (dat.p i) / workloadOperator dat Q dat.lam (dat.p i) - 1) :=
    fun i => Finset.inf'_le _ (Finset.mem_univ i)
  set C : ℝ := ∑ i, ∑ j, |Q i j| + 1 with hC
  have hCpos : 0 < C := by positivity
  refine ⟨C / ε, div_pos hCpos hεpos, fun Dh Fh Th Zh hsol t ht => ?_⟩
  obtain ⟨hfl, hhl⟩ := hsol
  have hdrift : ∀ (j : Fin I) (t : ℝ), 0 < t → 0 < Zh t j →
      ∀ d : ℝ, HasDerivAt (fun s => Dh s j) d t → totalArrivalRates dat Q j + ε ≤ d := by
    intro j s hs hz d hd
    have hTD : (fun u => Th u j) =ᶠ[nhds s] (fun u => dat.m j * Dh u j) := by
      filter_upwards [lt_mem_nhds hs] with u hu
      rw [hfl.2.2.1 u hu.le j, hfl.2.2.2.1 u hu.le j]
    have hT : HasDerivAt (fun u => Th u j) (dat.m j * d) s :=
      (hd.const_mul (dat.m j)).congr_of_eventuallyEq hTD
    have heq := hhl j s hs hz _ hT
    unfold proportionVector at heq
    have hm := dat.m_pos j
    have hρ := hρpos j
    have hdval : d = dat.b (dat.p j) * α j / workloadOperator dat Q dat.lam (dat.p j) := by
      field_simp at heq ⊢
      simp only [hα]
      nlinarith [heq]
    rw [hdval]
    have := hεle j
    simp only [hα] at this ⊢
    rw [mul_sub, mul_one, mul_div_assoc'] at this
    rw [mul_comm (dat.b (dat.p j))]
    linarith
  refine dre_core dat Q hQ dat.m_pos dat.b_pos dat.P_nonneg dat.P_transient Dh Fh Th Zh hfl ε hεpos
    hdrift t ?_
  have hZ0 : ∀ j, 0 ≤ Zh 0 j := hfl.2.1 0 le_rfl
  have hsum : ∑ i, (Q.mulVec (Zh 0)) i ≤ C * ∑ j, Zh 0 j := by
    calc ∑ i, (Q.mulVec (Zh 0)) i = ∑ i, ∑ j, Q i j * Zh 0 j := by
          simp [Matrix.mulVec, dotProduct]
      _ ≤ ∑ i, ∑ j, |Q i j| * Zh 0 j :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_right (le_abs_self _) (hZ0 j)
      _ = ∑ j, (∑ i, |Q i j|) * Zh 0 j := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
      _ ≤ ∑ j, C * Zh 0 j := by
          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (hZ0 j)
          have : ∑ i, |Q i j| ≤ ∑ i, ∑ j', |Q i j'| :=
            Finset.sum_le_sum fun i _ => Finset.single_le_sum (f := fun j' => |Q i j'|)
              (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
          linarith
      _ = C * ∑ j, Zh 0 j := by rw [Finset.mul_sum]
  rw [div_le_iff₀ hεpos]
  rw [div_mul_eq_mul_div, div_le_iff₀ hεpos] at ht
  nlinarith


