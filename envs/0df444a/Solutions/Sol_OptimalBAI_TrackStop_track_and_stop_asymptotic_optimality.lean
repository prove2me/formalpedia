-- Prove2me | solution 1 for OptimalBAI.TrackStop.track_and_stop_asymptotic_optimality
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T16:33:26.372764+00:00
-- url     : https://prove2.me/submissions/3df4a7c6-e9e3-4385-b25e-a00a942aa1e7

/-
Released under Apache 2.0 license.
Written by Codex.
-/
import Mathlib
import Definitions.Def_OptimalBAI_OptProportions_ExpFamily
import Definitions.Def_OptimalBAI_OptProportions_OptimalProportions
import Definitions.Def_OptimalBAI_TrackStop_ChernoffRule
import Definitions.Def_OptimalBAI_TrackStop_ExpFamily
import Definitions.Def_OptimalBAI_TrackStop_Tracking



open Set Filter Topology

namespace OptimalBAI.OptProportions.ExpFamily

variable (F : ExpFamily)

lemma parameter_convex : Convex ℝ F.Θ := F.ordConnected_Θ.convex

lemma b_differentiableAt {t : ℝ} (ht : t ∈ F.Θ) : DifferentiableAt ℝ F.b t :=
  (F.contDiff.differentiableOn (by norm_num) t ht).differentiableAt
    (F.isOpen_Θ.mem_nhds ht)

lemma mean_contDiff : ContDiffOn ℝ 1 (deriv F.b) F.Θ :=
  F.contDiff.deriv_of_isOpen F.isOpen_Θ (by norm_num)

lemma mean_differentiableAt {t : ℝ} (ht : t ∈ F.Θ) :
    DifferentiableAt ℝ (deriv F.b) t :=
  (F.mean_contDiff.differentiableOn (by norm_num) t ht).differentiableAt
    (F.isOpen_Θ.mem_nhds ht)

lemma mean_strictMono : StrictMonoOn (deriv F.b) F.Θ := by
  apply strictMonoOn_of_deriv_pos F.parameter_convex F.mean_contDiff.continuousOn
  intro t ht
  exact F.deriv2_pos t (interior_subset ht)

lemma b_strictConvex : StrictConvexOn ℝ F.Θ F.b := by
  apply strictConvexOn_of_deriv2_pos F.parameter_convex F.contDiff.continuousOn
  intro t ht
  exact F.deriv2_pos t (interior_subset ht)

lemma parameter_mem {u : ℝ} (hu : u ∈ F.M) : F.θof u ∈ F.Θ :=
  Function.invFunOn_mem hu

lemma mean_parameter {u : ℝ} (hu : u ∈ F.M) : deriv F.b (F.θof u) = u :=
  Function.invFunOn_eq hu

lemma parameter_mean {t : ℝ} (ht : t ∈ F.Θ) : F.θof (deriv F.b t) = t :=
  F.mean_strictMono.injOn.leftInvOn_invFunOn ht

lemma parameter_strictMono : StrictMonoOn F.θof F.M := by
  intro u hu v hv huv
  by_contra h
  have hle : F.θof v ≤ F.θof u := le_of_not_gt h
  have := F.mean_strictMono.monotoneOn (F.parameter_mem hv) (F.parameter_mem hu) hle
  rw [F.mean_parameter hv, F.mean_parameter hu] at this
  exact (not_le_of_gt huv) this

lemma mean_ordConnected : F.M.OrdConnected :=
  (F.ordConnected_Θ.isPreconnected.image (deriv F.b) F.mean_contDiff.continuousOn).ordConnected

lemma mean_isOpen : IsOpen F.M := by
  rw [isOpen_iff_mem_nhds]
  rintro u ⟨t, ht, rfl⟩
  obtain ⟨l, r, hlr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (F.isOpen_Θ.mem_nhds ht)
  obtain ⟨l', hll', hl't⟩ := exists_between hlr.1
  obtain ⟨r', htr', hr'r⟩ := exists_between hlr.2
  have hl' : l' ∈ F.Θ := hsub ⟨hll', hl't.trans hlr.2⟩
  have hr' : r' ∈ F.Θ := hsub ⟨hlr.1.trans htr', hr'r⟩
  refine mem_of_superset (Ioo_mem_nhds (F.mean_strictMono hl' ht hl't)
    (F.mean_strictMono ht hr' htr')) ?_
  intro v hv
  have hm := F.mean_ordConnected.out
    (show deriv F.b l' ∈ F.M from ⟨l', hl', rfl⟩)
    (show deriv F.b r' ∈ F.M from ⟨r', hr', rfl⟩)
    ⟨hv.1.le, hv.2.le⟩
  exact hm

lemma parameter_image : F.θof '' F.M = F.Θ := by
  apply Subset.antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact F.parameter_mem hu
  · intro t ht
    exact ⟨deriv F.b t, ⟨t, ht, rfl⟩, F.parameter_mean ht⟩

lemma parameter_continuousAt {u : ℝ} (hu : u ∈ F.M) : ContinuousAt F.θof u := by
  apply F.parameter_strictMono.continuousAt_of_image_mem_nhds (F.mean_isOpen.mem_nhds hu)
  rw [F.parameter_image]
  exact F.isOpen_Θ.mem_nhds (F.parameter_mem hu)

lemma parameter_hasDerivAt {u : ℝ} (hu : u ∈ F.M) :
    HasDerivAt F.θof (deriv (deriv F.b) (F.θof u))⁻¹ u := by
  apply HasDerivAt.of_local_left_inverse (F.parameter_continuousAt hu)
    (F.mean_differentiableAt (F.parameter_mem hu)).hasDerivAt
    (ne_of_gt (F.deriv2_pos _ (F.parameter_mem hu)))
  filter_upwards [F.mean_isOpen.mem_nhds hu] with v hv
  exact F.mean_parameter hv

lemma d_self (u : ℝ) : F.d u u = 0 := by simp [d]

lemma d_pos {u v : ℝ} (hu : u ∈ F.M) (hv : v ∈ F.M) (hne : u ≠ v) : 0 < F.d u v := by
  have hparam : F.θof u ≠ F.θof v := by
    intro h
    apply hne
    rw [← F.mean_parameter hu, ← F.mean_parameter hv, h]
  rcases lt_or_gt_of_ne hparam with hlt | hgt
  · have hs := F.b_strictConvex.lt_slope_of_hasDerivAt
      (F.parameter_mem hu) (F.parameter_mem hv) hlt (F.b_differentiableAt (F.parameter_mem hu)).hasDerivAt
    rw [F.mean_parameter hu, slope_def_field] at hs
    have := (lt_div_iff₀ (sub_pos.mpr hlt)).mp hs
    dsimp [d]
    linarith
  · have hs := F.b_strictConvex.slope_lt_of_hasDerivAt
      (F.parameter_mem hv) (F.parameter_mem hu) hgt (F.b_differentiableAt (F.parameter_mem hu)).hasDerivAt
    rw [F.mean_parameter hu, slope_def_field] at hs
    have := (div_lt_iff₀ (sub_pos.mpr hgt)).mp hs
    dsimp [d]
    nlinarith

lemma d_nonneg {u v : ℝ} (hu : u ∈ F.M) (hv : v ∈ F.M) : 0 ≤ F.d u v := by
  by_cases h : u = v
  · subst v; simp [F.d_self]
  · exact (F.d_pos hu hv h).le

lemma d_hasDerivAt_right {u v : ℝ} (hv : v ∈ F.M) :
    HasDerivAt (F.d u)
      ((v - u) * (deriv (deriv F.b) (F.θof v))⁻¹) v := by
  letI : NormedSpace ℝ ℝ := NormedField.toNormedSpace
  have ht := F.parameter_hasDerivAt hv
  have hb := (F.b_differentiableAt (F.parameter_mem hv)).hasDerivAt.comp v ht
  rw [F.mean_parameter hv] at hb
  have hd : HasDerivAt (F.d u)
      (v * (deriv (deriv F.b) (F.θof v))⁻¹ - u * (deriv (deriv F.b) (F.θof v))⁻¹) v := by
    convert (hb.sub_const (F.b (F.θof u))).sub ((ht.sub_const (F.θof u)).const_mul u) using 1 <;> rfl
  convert hd using 1 <;> ring

lemma d_continuousAt_right {u v : ℝ} (hv : v ∈ F.M) : ContinuousAt (F.d u) v :=
  (F.d_hasDerivAt_right hv).continuousAt

end OptimalBAI.OptProportions.ExpFamily


open Set Filter Topology

namespace OptimalBAI.OptProportions

noncomputable def mix (u v x : ℝ) : ℝ := (u + x * v) / (1 + x)

lemma mix_eq (u v x : ℝ) (hx : 1 + x ≠ 0) :
    mix u v x = v + (u - v) / (1 + x) := by
  unfold mix
  field_simp
  ring

lemma mix_bounds {u v x : ℝ} (hvu : v < u) (hx : 0 ≤ x) :
    v < mix u v x ∧ mix u v x ≤ u := by
  have hd : 0 < 1 + x := by linarith
  rw [mix_eq u v x hd.ne']
  constructor
  · have := div_pos (sub_pos.mpr hvu) hd
    linarith
  · have hdiv : (u - v) / (1 + x) ≤ u - v := by
      apply (div_le_iff₀ hd).mpr
      nlinarith
    linarith

lemma mix_mem (F : ExpFamily) {u v x : ℝ} (hu : u ∈ F.M) (hv : v ∈ F.M)
    (hvu : v < u) (hx : 0 ≤ x) : mix u v x ∈ F.M :=
  F.mean_ordConnected.out hv hu ⟨(mix_bounds hvu hx).1.le, (mix_bounds hvu hx).2⟩

lemma mix_hasDerivAt (u v x : ℝ) (hx : 1 + x ≠ 0) :
    HasDerivAt (mix u v) ((v - u) / (1 + x)^2) x := by
  have hn := (hasDerivAt_const x u).add ((hasDerivAt_id x).mul_const v)
  have hd := (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
  convert hn.div hd hx using 1 <;> first | rfl | ((try dsimp [mix]); ring)

lemma gFun_eq {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ) (a : Fin K)
    (x : ℝ) (hx : 1 + x ≠ 0) :
    gFun F μ a x = F.d (μ 0) (mix (μ 0) (μ a) x) +
      x * F.d (μ a) (mix (μ 0) (μ a) x) := by
  have hm : 1 / (1 + x) * μ 0 + (1 - 1 / (1 + x)) * μ a = mix (μ 0) (μ a) x := by
    unfold mix
    field_simp
    ring
  unfold gFun jensenShannon
  rw [hm]
  field_simp
  ring

lemma gFun_zero {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ) (a : Fin K) :
    gFun F μ a 0 = 0 := by
  rw [gFun_eq F μ a 0 (by norm_num)]
  simp [mix, F.d_self]

lemma gFun_hasDerivAt {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ)
    (a : Fin K) {x : ℝ} (hx : 0 ≤ x) (hm : mix (μ 0) (μ a) x ∈ F.M) :
    HasDerivAt (gFun F μ a) (F.d (μ a) (mix (μ 0) (μ a) x)) x := by
  have hden : 1 + x ≠ 0 := by linarith
  have hmix := mix_hasDerivAt (μ 0) (μ a) x hden
  have hdu := (F.d_hasDerivAt_right (u := μ 0) hm).comp x hmix
  have hdv := (F.d_hasDerivAt_right (u := μ a) hm).comp x hmix
  have h := hdu.add ((hasDerivAt_id x).mul hdv)
  have h' : HasDerivAt (fun t => F.d (μ 0) (mix (μ 0) (μ a) t) +
      t * F.d (μ a) (mix (μ 0) (μ a) t)) (F.d (μ a) (mix (μ 0) (μ a) x)) x := by
    convert h using 1 <;> first | rfl | ((try dsimp [mix]); field_simp; ring)
  apply h'.congr_of_eventuallyEq
  have hc : ContinuousAt (fun t : ℝ => 1 + t) x := continuousAt_const.add continuousAt_id
  filter_upwards [hc.eventually_ne hden] with t ht
  exact gFun_eq F μ a t ht

lemma gFun_continuousOn {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (a : Fin K) (ha : a ≠ 0) :
    ContinuousOn (gFun F μ a) (Ici 0) := by
  intro x hx
  exact (gFun_hasDerivAt F μ a hx (mix_mem F (hμ 0) (hμ a) (hbest a ha) hx)).continuousAt.continuousWithinAt

lemma gFun_strictMono {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (a : Fin K) (ha : a ≠ 0) :
    StrictMonoOn (gFun F μ a) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) (gFun_continuousOn F μ hμ hbest a ha)
  intro x hx
  have hx0 : 0 ≤ x := interior_subset hx
  have hm := mix_mem F (hμ 0) (hμ a) (hbest a ha) hx0
  rw [(gFun_hasDerivAt F μ a hx0 hm).deriv]
  exact F.d_pos (hμ a) hm (ne_of_lt (mix_bounds (hbest a ha) hx0).1)

lemma mix_tendsto (u v : ℝ) : Tendsto (mix u v) atTop (𝓝 v) := by
  have hd : Tendsto (fun x : ℝ => 1 + x) atTop atTop :=
    tendsto_atTop_mono (fun x : ℝ => by dsimp; linarith) tendsto_id
  have hi : Tendsto (fun x : ℝ => (1 + x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hd
  have h : Tendsto (fun x : ℝ => v + (u - v) * (1 + x)⁻¹) atTop (𝓝 v) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hi)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [mix_eq u v x (by linarith), div_eq_mul_inv]

lemma d_symm_sum (F : ExpFamily) (u v : ℝ) :
    F.d u v + F.d v u = (v - u) * (F.θof v - F.θof u) := by
  unfold ExpFamily.d
  ring

lemma weighted_d_bound (F : ExpFamily) {u v x : ℝ} (hu : u ∈ F.M)
    (hv : v ∈ F.M) (hvu : v < u) (hx : 0 ≤ x) :
    0 ≤ x * F.d v (mix u v x) ∧
    x * F.d v (mix u v x) ≤ (u - v) * (F.θof (mix u v x) - F.θof v) := by
  have hm := mix_mem F hu hv hvu hx
  have hvm := (mix_bounds hvu hx).1
  have ht : 0 ≤ F.θof (mix u v x) - F.θof v :=
    sub_nonneg.mpr (F.parameter_strictMono hv hm hvm).le
  have hd := F.d_nonneg hm hv
  have hsum := d_symm_sum F v (mix u v x)
  have hxmix : x * (mix u v x - v) ≤ u - v := by
    have hden : 0 < 1 + x := by linarith
    rw [mix_eq u v x hden.ne']
    have hid : x * (v + (u - v) / (1 + x) - v) = x * (u - v) / (1 + x) := by ring
    rw [hid]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  constructor
  · exact mul_nonneg hx (F.d_nonneg hv hm)
  · calc
      x * F.d v (mix u v x) ≤ x * ((mix u v x - v) * (F.θof (mix u v x) - F.θof v)) :=
        mul_le_mul_of_nonneg_left (by linarith) hx
      _ = (x * (mix u v x - v)) * (F.θof (mix u v x) - F.θof v) := by ring
      _ ≤ (u - v) * (F.θof (mix u v x) - F.θof v) := mul_le_mul_of_nonneg_right hxmix ht

lemma gFun_tendsto {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (a : Fin K) (ha : a ≠ 0) :
    Tendsto (gFun F μ a) atTop (𝓝 (F.d (μ 0) (μ a))) := by
  have hm := mix_tendsto (μ 0) (μ a)
  have hd := (F.d_continuousAt_right (u := μ 0) (hμ a)).tendsto.comp hm
  have ht := (F.parameter_continuousAt (hμ a)).tendsto.comp hm
  have htd : Tendsto (fun x => F.θof (mix (μ 0) (μ a) x) - F.θof (μ a)) atTop (𝓝 0) := by
    simpa using ht.sub (tendsto_const_nhds (x := F.θof (μ a)))
  have hbound : Tendsto (fun x => (μ 0 - μ a) * (F.θof (mix (μ 0) (μ a) x) - F.θof (μ a)))
      atTop (𝓝 0) := by
    simpa using htd.const_mul (μ 0 - μ a)
  have hz : Tendsto (fun x => x * F.d (μ a) (mix (μ 0) (μ a) x)) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hbound
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      exact (weighted_d_bound F (hμ 0) (hμ a) (hbest a ha) hx).1
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      exact (weighted_d_bound F (hμ 0) (hμ a) (hbest a ha) hx).2
  have h := hd.add hz
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact (gFun_eq F μ a x (by linarith)).symm

lemma gFun_lt_limit {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (a : Fin K) (ha : a ≠ 0)
    {x : ℝ} (hx : 0 ≤ x) : gFun F μ a x < F.d (μ 0) (μ a) := by
  have hmono := gFun_strictMono F μ hμ hbest a ha
  have hle : gFun F μ a (x + 1) ≤ F.d (μ 0) (μ a) := by
    apply ge_of_tendsto (gFun_tendsto F μ hμ hbest a ha)
    filter_upwards [eventually_ge_atTop (x + 1)] with t ht
    exact hmono.monotoneOn (by simp; linarith) (by simp; linarith) ht
  exact (hmono hx (by simp; linarith) (by linarith)).trans_le hle

lemma gFun_image {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (a : Fin K) (ha : a ≠ 0) :
    gFun F μ a '' Ici 0 = Ico 0 (F.d (μ 0) (μ a)) := by
  have hmono := gFun_strictMono F μ hμ hbest a ha
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, gFun_lt_limit F μ hμ hbest a ha hx⟩
    simpa only [gFun_zero] using hmono.monotoneOn (show (0 : ℝ) ∈ Ici 0 from by simp) hx hx
  · intro y hy
    have hev : ∀ᶠ x : ℝ in atTop, y < gFun F μ a x :=
      (gFun_tendsto F μ hμ hbest a ha).eventually (eventually_gt_nhds hy.2)
    obtain ⟨x, hx, hxy⟩ := (eventually_ge_atTop (0 : ℝ)).and hev |>.exists
    have hcont := (gFun_continuousOn F μ hμ hbest a ha).mono
      (show Icc 0 x ⊆ Ici 0 from fun _ hz => hz.1)
    have hym : y ∈ Icc (gFun F μ a 0) (gFun F μ a x) := by
      rw [gFun_zero]
      exact ⟨hy.1, hxy.le⟩
    obtain ⟨z, hz, hzy⟩ := intermediate_value_Icc hx hcont hym
    exact ⟨z, hz.1, hzy⟩

end OptimalBAI.OptProportions


open Set Filter Topology

namespace OptimalBAI.OptProportions

variable {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ)
  (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (a : Fin K) (ha : a ≠ 0)

include hμ hbest ha

lemma xFun_mem {y : ℝ} (hy : y ∈ Ico 0 (F.d (μ 0) (μ a))) :
    xFun F μ a y ∈ Ici 0 := by
  unfold xFun
  rw [if_neg ha]
  apply Function.invFunOn_mem
  change y ∈ gFun F μ a '' Ici 0
  rw [gFun_image F μ hμ hbest a ha]
  exact hy

lemma gFun_xFun {y : ℝ} (hy : y ∈ Ico 0 (F.d (μ 0) (μ a))) :
    gFun F μ a (xFun F μ a y) = y := by
  unfold xFun
  rw [if_neg ha]
  apply Function.invFunOn_eq
  change y ∈ gFun F μ a '' Ici 0
  rw [gFun_image F μ hμ hbest a ha]
  exact hy

lemma xFun_gFun {x : ℝ} (hx : 0 ≤ x) : xFun F μ a (gFun F μ a x) = x := by
  unfold xFun
  rw [if_neg ha]
  exact (gFun_strictMono F μ hμ hbest a ha).injOn.leftInvOn_invFunOn hx

lemma xFun_zero : xFun F μ a 0 = 0 := by
  simpa only [gFun_zero] using xFun_gFun F μ hμ hbest a ha (x := 0) le_rfl

lemma xFun_strictMono : StrictMonoOn (xFun F μ a) (Ico 0 (F.d (μ 0) (μ a))) := by
  intro y hy z hz hyz
  by_contra h
  have hle : xFun F μ a z ≤ xFun F μ a y := le_of_not_gt h
  have h := (gFun_strictMono F μ hμ hbest a ha).monotoneOn
    (xFun_mem F μ hμ hbest a ha hz) (xFun_mem F μ hμ hbest a ha hy) hle
  rw [gFun_xFun F μ hμ hbest a ha hz, gFun_xFun F μ hμ hbest a ha hy] at h
  exact (not_le_of_gt hyz) h

lemma xFun_image : xFun F μ a '' Ico 0 (F.d (μ 0) (μ a)) = Ici 0 := by
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact xFun_mem F μ hμ hbest a ha hy
  · intro x hx
    refine ⟨gFun F μ a x, ?_, xFun_gFun F μ hμ hbest a ha hx⟩
    rw [← gFun_image F μ hμ hbest a ha]
    exact ⟨x, hx, rfl⟩

lemma xFun_pos {y : ℝ} (hy0 : 0 < y) (hyD : y < F.d (μ 0) (μ a)) :
    0 < xFun F μ a y := by
  have hD : 0 < F.d (μ 0) (μ a) := F.d_pos (hμ 0) (hμ a) (ne_of_gt (hbest a ha))
  have h := xFun_strictMono F μ hμ hbest a ha (show (0 : ℝ) ∈ Ico 0 _ from ⟨le_rfl, hD⟩)
    ⟨hy0.le, hyD⟩ hy0
  simpa only [xFun_zero F μ hμ hbest a ha] using h

lemma xFun_continuousAt {y : ℝ} (hy0 : 0 < y) (hyD : y < F.d (μ 0) (μ a)) :
    ContinuousAt (xFun F μ a) y := by
  apply (xFun_strictMono F μ hμ hbest a ha).continuousAt_of_image_mem_nhds
    (Ico_mem_nhds hy0 hyD)
  rw [xFun_image F μ hμ hbest a ha]
  exact Ici_mem_nhds (xFun_pos F μ hμ hbest a ha hy0 hyD)

lemma xFun_continuousOn : ContinuousOn (xFun F μ a) (Ico 0 (F.d (μ 0) (μ a))) := by
  intro y hy
  rcases eq_or_lt_of_le hy.1 with hy0 | hy0
  · subst y
    have hD : 0 < F.d (μ 0) (μ a) := hy.2
    apply ((xFun_strictMono F μ hμ hbest a ha).continuousWithinAt_right_of_image_mem_nhdsWithin
      (Ico_mem_nhdsGE hD) ?_).mono Ico_subset_Ici_self
    rw [xFun_image F μ hμ hbest a ha, xFun_zero F μ hμ hbest a ha]
    exact self_mem_nhdsWithin
  · exact (xFun_continuousAt F μ hμ hbest a ha hy0 hy.2).continuousWithinAt

lemma xFun_hasDerivAt {y : ℝ} (hy0 : 0 < y) (hyD : y < F.d (μ 0) (μ a)) :
    HasDerivAt (xFun F μ a)
      (F.d (μ a) (mix (μ 0) (μ a) (xFun F μ a y)))⁻¹ y := by
  have hx : 0 ≤ xFun F μ a y := xFun_mem F μ hμ hbest a ha ⟨hy0.le, hyD⟩
  have hm := mix_mem F (hμ 0) (hμ a) (hbest a ha) hx
  apply HasDerivAt.of_local_left_inverse (xFun_continuousAt F μ hμ hbest a ha hy0 hyD)
    (gFun_hasDerivAt F μ a hx hm)
    (ne_of_gt (F.d_pos (hμ a) hm (ne_of_lt (mix_bounds (hbest a ha) hx).1)))
  filter_upwards [Ico_mem_nhds hy0 hyD] with z hz
  exact gFun_xFun F μ hμ hbest a ha hz

lemma xFun_tendsto_atTop : Tendsto (xFun F μ a)
    (𝓝[<] (F.d (μ 0) (μ a))) atTop := by
  apply tendsto_atTop.2
  intro c
  let r := max 0 c
  have hr : 0 ≤ r := le_max_left _ _
  have hgd := gFun_lt_limit F μ hμ hbest a ha hr
  have hgn : 0 ≤ gFun F μ a r := by
    have h := (gFun_strictMono F μ hμ hbest a ha).monotoneOn (show (0 : ℝ) ∈ Ici 0 from by simp) hr hr
    simpa only [gFun_zero] using h
  filter_upwards [(eventually_gt_nhds hgd).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with y hy hyD
  have hym : y ∈ Ico 0 (F.d (μ 0) (μ a)) := ⟨hgn.trans hy.le, hyD⟩
  have hgrm : gFun F μ a r ∈ Ico 0 (F.d (μ 0) (μ a)) := ⟨hgn, hgd⟩
  have h := xFun_strictMono F μ hμ hbest a ha hgrm hym hy
  rw [xFun_gFun F μ hμ hbest a ha hr] at h
  exact (le_max_right (0 : ℝ) c).trans h.le

end OptimalBAI.OptProportions


open Set Filter Topology

namespace OptimalBAI.OptProportions

namespace ExpFamily

lemma d_right_strictMono (F : ExpFamily) (v : ℝ) : StrictMonoOn (F.d v) (F.M ∩ Ici v) := by
  apply strictMonoOn_of_deriv_pos (F.mean_ordConnected.convex.inter (convex_Ici v))
  · intro t ht
    exact (F.d_continuousAt_right ht.1).continuousWithinAt
  · intro t ht
    have hM : t ∈ F.M := (interior_subset ht).1
    have hv : v < t := by
      have h := interior_mono (inter_subset_right : F.M ∩ Ici v ⊆ Ici v) ht
      simpa only [interior_Ici, mem_Ioi] using h
    rw [(F.d_hasDerivAt_right (u := v) hM).deriv]
    exact mul_pos (sub_pos.mpr hv) (inv_pos.mpr (F.deriv2_pos _ (F.parameter_mem hM)))

lemma d_right_strictAnti (F : ExpFamily) (u : ℝ) : StrictAntiOn (F.d u) (F.M ∩ Iic u) := by
  apply strictAntiOn_of_deriv_neg (F.mean_ordConnected.convex.inter (convex_Iic u))
  · intro t ht
    exact (F.d_continuousAt_right ht.1).continuousWithinAt
  · intro t ht
    have hM : t ∈ F.M := (interior_subset ht).1
    have hu : t < u := by
      have h := interior_mono (inter_subset_right : F.M ∩ Iic u ⊆ Iic u) ht
      simpa only [interior_Iic, mem_Iio] using h
    rw [(F.d_hasDerivAt_right (u := u) hM).deriv]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hu) (inv_pos.mpr (F.deriv2_pos _ (F.parameter_mem hM)))

end ExpFamily

lemma mix_strictAnti {u v : ℝ} (hvu : v < u) : StrictAntiOn (mix u v) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · intro x hx
    exact (mix_hasDerivAt u v x (by linarith [show 0 ≤ x from hx])).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 ≤ x := interior_subset hx
    rw [(mix_hasDerivAt u v x (by linarith)).deriv]
    exact div_neg_of_neg_of_pos (sub_neg.mpr hvu) (sq_pos_of_ne_zero (by linarith))

noncomputable def allocationRatio (F : ExpFamily) (u v x : ℝ) : ℝ :=
  F.d u (mix u v x) / F.d v (mix u v x)

lemma allocationRatio_nonneg (F : ExpFamily) {u v x : ℝ} (hu : u ∈ F.M) (hv : v ∈ F.M)
    (hvu : v < u) (hx : 0 ≤ x) : 0 ≤ allocationRatio F u v x := by
  have hm := mix_mem F hu hv hvu hx
  exact div_nonneg (F.d_nonneg hu hm) (F.d_nonneg hv hm)

lemma allocationRatio_zero (F : ExpFamily) (u v : ℝ) : allocationRatio F u v 0 = 0 := by
  simp [allocationRatio, mix, F.d_self]

lemma allocationRatio_continuousAt (F : ExpFamily) {u v x : ℝ} (hu : u ∈ F.M)
    (hv : v ∈ F.M) (hvu : v < u) (hx : 0 ≤ x) : ContinuousAt (allocationRatio F u v) x := by
  have hm := mix_mem F hu hv hvu hx
  have hc := (mix_hasDerivAt u v x (by linarith)).continuousAt
  exact ((F.d_continuousAt_right (u := u) hm).comp hc).div
    ((F.d_continuousAt_right (u := v) hm).comp hc)
    (ne_of_gt (F.d_pos hv hm (ne_of_lt (mix_bounds hvu hx).1)))

lemma allocationRatio_strictMono (F : ExpFamily) {u v : ℝ} (hu : u ∈ F.M)
    (hv : v ∈ F.M) (hvu : v < u) : StrictMonoOn (allocationRatio F u v) (Ici 0) := by
  intro x hx y hy hxy
  have hmx := mix_mem F hu hv hvu hx
  have hmy := mix_mem F hu hv hvu hy
  have hmxbd := mix_bounds hvu hx
  have hmybd := mix_bounds hvu hy
  have hmix := mix_strictAnti hvu hx hy hxy
  have hnum := F.d_right_strictAnti u ⟨hmy, hmybd.2⟩ ⟨hmx, hmxbd.2⟩ hmix
  have hden := F.d_right_strictMono v ⟨hmy, hmybd.1.le⟩ ⟨hmx, hmxbd.1.le⟩ hmix
  have hyden := F.d_pos hv hmy (ne_of_lt hmybd.1)
  unfold allocationRatio
  exact (div_le_div_of_nonneg_left (F.d_nonneg hu hmx) hyden hden.le).trans_lt
    (div_lt_div_of_pos_right hnum hyden)

lemma allocationRatio_tendsto (F : ExpFamily) {u v : ℝ} (hu : u ∈ F.M)
    (hv : v ∈ F.M) (hvu : v < u) : Tendsto (allocationRatio F u v) atTop atTop := by
  have hm := mix_tendsto u v
  have hn := (F.d_continuousAt_right (u := u) hv).tendsto.comp hm
  have hd : Tendsto (fun x => F.d v (mix u v x)) atTop (𝓝 0) := by
    simpa only [F.d_self, Function.comp_def] using (F.d_continuousAt_right (u := v) hv).tendsto.comp hm
  have hd' : Tendsto (fun x => F.d v (mix u v x)) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hd, ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact F.d_pos hv (mix_mem F hu hv hvu hx) (ne_of_lt (mix_bounds hvu hx).1)
  have hi := hd'.inv_tendsto_nhdsGT_zero
  convert hn.pos_mul_atTop (F.d_pos hu hv (ne_of_gt hvu)) hi using 1 <;>
    first | rfl | (funext x; simp [allocationRatio, div_eq_mul_inv, Function.comp_def])

end OptimalBAI.OptProportions


open Set Filter Topology

namespace OptimalBAI.OptProportions

noncomputable def pairCost (F : ExpFamily) (u v p q : ℝ) : ℝ :=
  (p + q) * jensenShannon F (p / (p + q)) u v

noncomputable def pairMean (u v p q : ℝ) : ℝ :=
  if p + q = 0 then v else (p * u + q * v) / (p + q)

lemma weights_zero {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (h : p + q = 0) : p = 0 ∧ q = 0 := by
  constructor <;> linarith

lemma pairMean_balance {u v p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (p + q) * pairMean u v p q = p * u + q * v := by
  by_cases h : p + q = 0
  · obtain ⟨rfl, rfl⟩ := weights_zero hp hq h
    simp [pairMean]
  · simp only [pairMean, if_neg h]
    field_simp

lemma pairMean_bounds {u v p q : ℝ} (hvu : v ≤ u) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    v ≤ pairMean u v p q ∧ pairMean u v p q ≤ u := by
  by_cases h : p + q = 0
  · simp [pairMean, h, hvu]
  · have hd : 0 < p + q := lt_of_le_of_ne (add_nonneg hp hq) (Ne.symm h)
    simp only [pairMean, if_neg h]
    constructor
    · apply (le_div_iff₀ hd).mpr
      nlinarith
    · apply (div_le_iff₀ hd).mpr
      nlinarith

lemma pairMean_mem (F : ExpFamily) {u v p q : ℝ} (hu : u ∈ F.M) (hv : v ∈ F.M)
    (hvu : v ≤ u) (hp : 0 ≤ p) (hq : 0 ≤ q) : pairMean u v p q ∈ F.M :=
  F.mean_ordConnected.out hv hu (pairMean_bounds hvu hp hq)

lemma pairCost_eq (F : ExpFamily) {u v p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    pairCost F u v p q = p * F.d u (pairMean u v p q) + q * F.d v (pairMean u v p q) := by
  by_cases h : p + q = 0
  · obtain ⟨rfl, rfl⟩ := weights_zero hp hq h
    simp [pairCost]
  · have hm : p / (p + q) * u + (1 - p / (p + q)) * v = pairMean u v p q := by
      simp only [pairMean, if_neg h]
      field_simp
      ring
    unfold pairCost jensenShannon
    rw [hm]
    field_simp
    ring

lemma pairCost_nonneg (F : ExpFamily) {u v p q : ℝ} (hu : u ∈ F.M) (hv : v ∈ F.M)
    (hvu : v ≤ u) (hp : 0 ≤ p) (hq : 0 ≤ q) : 0 ≤ pairCost F u v p q := by
  have hm := pairMean_mem F hu hv hvu hp hq
  rw [pairCost_eq F hp hq]
  exact add_nonneg (mul_nonneg hp (F.d_nonneg hu hm)) (mul_nonneg hq (F.d_nonneg hv hm))

lemma weighted_pair_bound (F : ExpFamily) {u v p q s t : ℝ} (hu : u ∈ F.M)
    (hv : v ∈ F.M) (hvu : v ≤ u) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hs : s ∈ F.M) (ht : t ∈ F.M) (hst : s ≤ t) :
    pairCost F u v p q ≤ p * F.d u s + q * F.d v t := by
  let m := pairMean u v p q
  have hm : m ∈ F.M := pairMean_mem F hu hv hvu hp hq
  have hbal : (p + q) * m = p * u + q * v := pairMean_balance hp hq
  have hmu : m ≤ u := (pairMean_bounds hvu hp hq).2
  have hθ : 0 ≤ F.θof t - F.θof s :=
    sub_nonneg.mpr (F.parameter_strictMono.monotoneOn hs ht hst)
  have hidentity : p * F.d u s + q * F.d v t - (p * F.d u m + q * F.d v m) =
      p * F.d m s + q * F.d m t + p * (u - m) * (F.θof t - F.θof s) := by
    unfold ExpFamily.d
    linear_combination (F.θof t - F.θof m) * hbal
  have hn : 0 ≤ p * F.d m s + q * F.d m t + p * (u - m) * (F.θof t - F.θof s) :=
    add_nonneg (add_nonneg (mul_nonneg hp (F.d_nonneg hm hs))
      (mul_nonneg hq (F.d_nonneg hm ht))) (mul_nonneg (mul_nonneg hp (sub_nonneg.mpr hmu)) hθ)
  rw [pairCost_eq F hp hq]
  change p * F.d u m + q * F.d v m ≤ _
  linarith

lemma pairCost_left_zero (F : ExpFamily) (u v q : ℝ) : pairCost F u v 0 q = 0 := by
  simp [pairCost, jensenShannon, F.d_self]

lemma pairCost_right_zero (F : ExpFamily) (u v : ℝ) {p : ℝ} (hp : 0 ≤ p) :
    pairCost F u v p 0 = 0 := by
  by_cases h : p = 0
  · rw [h, pairCost_left_zero]
  · simp [pairCost, jensenShannon, h, F.d_self]

lemma pairCost_pos (F : ExpFamily) {u v p q : ℝ} (hu : u ∈ F.M) (hv : v ∈ F.M)
    (hvu : v < u) (hp : 0 < p) (hq : 0 < q) : 0 < pairCost F u v p q := by
  have hden : 0 < p + q := add_pos hp hq
  have hpm : pairMean u v p q < u := by
    simp only [pairMean, if_neg hden.ne']
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hm := pairMean_mem F hu hv hvu.le hp.le hq.le
  rw [pairCost_eq F hp.le hq.le]
  exact add_pos_of_pos_of_nonneg (mul_pos hp (F.d_pos hu hm (ne_of_gt hpm)))
    (mul_nonneg hq.le (F.d_nonneg hv hm))

lemma pairCost_ratio {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ) (a : Fin K)
    {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    pairCost F (μ 0) (μ a) p q = p * gFun F μ a (q / p) := by
  have hs : p + q ≠ 0 := by linarith
  have hden : 1 + q / p ≠ 0 := by positivity
  have hα : p / (p + q) = 1 / (1 + q / p) := by
    field_simp
  have hsum : p + q = p * (1 + q / p) := by field_simp
  unfold pairCost gFun
  rw [hα, hsum]
  ring

end OptimalBAI.OptProportions


open Set Filter Topology

namespace OptimalBAI.OptProportions

lemma isBest_unique {K : ℕ} {μ : Fin K → ℝ} {a b : Fin K}
    (ha : IsBest μ a) (hb : IsBest μ b) : a = b := by
  by_contra hab
  have h1 := ha b (Ne.symm hab)
  have h2 := hb a hab
  linarith

lemma other_arms_nonempty {K : ℕ} [NeZero K] (hK : 2 ≤ K) :
    (Finset.univ.erase (0 : Fin K)).Nonempty := by
  refine ⟨⟨1, by omega⟩, ?_⟩
  simp [Fin.ext_iff]

lemma transportCost_le_baseline {K : ℕ} [NeZero K] (F : ExpFamily) (μ w : Fin K → ℝ)
    (hbest : IsBest μ 0) (lam : Fin K → ℝ) (hlam : ∀ i, lam i ∈ F.M)
    (j : Fin K) (hj : j ≠ 0) (hmax : ∀ i, lam i ≤ lam j) :
    transportCost F μ w ≤ ((∑ i, w i * F.d (μ i) (lam i) : ℝ) : EReal) := by
  have hmean : Tendsto (fun t : ℝ => lam j + t) (𝓝 0) (𝓝 (lam j)) := by
    simpa using (tendsto_const_nhds (x := lam j)).add (tendsto_id (α := ℝ) (x := 𝓝 0))
  have hmeanEv : ∀ᶠ t : ℝ in 𝓝[>] 0, lam j + t ∈ F.M :=
    (hmean.eventually (F.mean_isOpen.mem_nhds (hlam j))).filter_mono nhdsWithin_le_nhds
  have hcost : Tendsto (fun t : ℝ => ∑ i, w i * F.d (μ i) (Function.update lam j (lam j + t) i))
      (𝓝 0) (𝓝 (∑ i, w i * F.d (μ i) (lam i))) := by
    apply tendsto_finsetSum
    intro i hi
    by_cases hij : i = j
    · subst i
      simpa only [Function.update_self, Function.comp_def] using
        ((F.d_continuousAt_right (u := μ j) (hlam j)).tendsto.comp hmean).const_mul (w j)
    · simp only [Function.update_of_ne hij]
      exact tendsto_const_nhds
  have hE : Tendsto (fun t : ℝ => ((∑ i, w i * F.d (μ i) (Function.update lam j (lam j + t) i) : ℝ) : EReal))
      (𝓝[>] (0 : ℝ)) (𝓝 ((∑ i, w i * F.d (μ i) (lam i) : ℝ) : EReal)) :=
    EReal.tendsto_coe.mpr (hcost.mono_left nhdsWithin_le_nhds)
  apply ge_of_tendsto hE
  filter_upwards [hmeanEv, self_mem_nhdsWithin] with t ht htpos
  have htpos' : 0 < t := htpos
  let alt := Function.update lam j (lam j + t)
  have hM : ∀ i, alt i ∈ F.M := by
    intro i
    by_cases hij : i = j
    · subst i; simpa [alt] using ht
    · simpa [alt, Function.update_of_ne hij] using hlam i
  have hbj : IsBest alt j := by
    intro i hij
    simp only [alt, Function.update_of_ne hij, Function.update_self]
    exact (hmax i).trans_lt (by linarith)
  have halt : alt ∈ Alt F μ := by
    refine ⟨⟨hM, ⟨j, hbj⟩⟩, ?_⟩
    intro i hbi hmui
    have hij := isBest_unique hbi hbj
    subst i
    have hm0 := hmui 0 (Ne.symm hj)
    exact (not_lt_of_gt (hbest j hj)) hm0
  unfold transportCost
  exact iInf_le_of_le alt (iInf_le_of_le halt le_rfl)

lemma transportCost_le_pair {K : ℕ} [NeZero K] (F : ExpFamily) (μ w : Fin K → ℝ)
    (hμ : ∀ i, μ i ∈ F.M) (hbest : IsBest μ 0) (hw : w ∈ simplex K)
    (a : Fin K) (ha : a ≠ 0) :
    transportCost F μ w ≤ (pairCost F (μ 0) (μ a) (w 0) (w a) : EReal) := by
  classical
  let m := pairMean (μ 0) (μ a) (w 0) (w a)
  have hm : m ∈ F.M := pairMean_mem F (hμ 0) (hμ a) (hbest a ha).le (hw.1 0) (hw.1 a)
  let lam := fun i : Fin K => if i = 0 ∨ i = a then m else μ i
  have hlam : ∀ i, lam i ∈ F.M := by
    intro i
    by_cases hi : i = 0 ∨ i = a
    · simpa [lam, hi] using hm
    · simpa [lam, hi] using hμ i
  have hnonempty : (Finset.univ.erase (0 : Fin K)).Nonempty := ⟨a, by simp [ha]⟩
  obtain ⟨j, hjmem, hjmax⟩ := (Finset.univ.erase (0 : Fin K)).exists_max_image lam hnonempty
  have hj : j ≠ 0 := (Finset.mem_erase.mp hjmem).1
  have hmax : ∀ i, lam i ≤ lam j := by
    intro i
    by_cases hi : i = 0
    · subst i
      have hamem : a ∈ Finset.univ.erase (0 : Fin K) := by simp [ha]
      have := hjmax a hamem
      simpa [lam] using this
    · exact hjmax i (by simp [hi])
  have hupper := transportCost_le_baseline F μ w hbest lam hlam j hj hmax
  have hsum : ∑ i, w i * F.d (μ i) (lam i) =
      w 0 * F.d (μ 0) m + w a * F.d (μ a) m := by
    have hz : ∀ i ∈ (Finset.univ : Finset (Fin K)), i ∉ ({0, a} : Finset (Fin K)) →
        w i * F.d (μ i) (lam i) = 0 := by
      intro i hi hnot
      have hi0 : i ≠ 0 := by intro h; apply hnot; simp [h]
      have hia : i ≠ a := by intro h; apply hnot; simp [h]
      simp [lam, hi0, hia, F.d_self]
    rw [← Finset.sum_subset (Finset.subset_univ ({0, a} : Finset (Fin K))) hz]
    rw [Finset.sum_pair (Ne.symm ha)]
    simp [lam]
  rw [hsum, ← pairCost_eq F (hw.1 0) (hw.1 a)] at hupper
  exact hupper

lemma pairCost_le_alternative {K : ℕ} [NeZero K] (F : ExpFamily) (μ w : Fin K → ℝ)
    (hμ : ∀ i, μ i ∈ F.M) (hbest : IsBest μ 0) (hw : w ∈ simplex K)
    (lam : Fin K → ℝ) (halt : lam ∈ Alt F μ) :
    ∃ a : Fin K, a ≠ 0 ∧
      pairCost F (μ 0) (μ a) (w 0) (w a) ≤ ∑ i, w i * F.d (μ i) (lam i) := by
  classical
  obtain ⟨a, hba⟩ := halt.1.2
  have ha : a ≠ 0 := by
    intro h
    subst a
    exact halt.2 0 hba hbest
  refine ⟨a, ha, ?_⟩
  have hLam := halt.1.1
  have hpair := weighted_pair_bound F (hμ 0) (hμ a) (hbest a ha).le (hw.1 0) (hw.1 a)
    (hLam 0) (hLam a) (hba 0 (Ne.symm ha)).le
  have hs : w 0 * F.d (μ 0) (lam 0) + w a * F.d (μ a) (lam a) ≤
      ∑ i, w i * F.d (μ i) (lam i) := by
    rw [← Finset.sum_pair (f := fun i => w i * F.d (μ i) (lam i)) (Ne.symm ha)]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro i hi hnot
    exact mul_nonneg (hw.1 i) (F.d_nonneg (hμ i) (hLam i))
  exact hpair.trans hs

lemma transportCost_min_pair {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ)
    (hK : 2 ≤ K) (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0)
    (w : Fin K → ℝ) (hw : w ∈ simplex K) :
    ∃ a : Fin K, a ≠ 0 ∧
      (∀ b : Fin K, b ≠ 0 → pairCost F (μ 0) (μ a) (w 0) (w a) ≤
        pairCost F (μ 0) (μ b) (w 0) (w b)) ∧
      transportCost F μ w = (pairCost F (μ 0) (μ a) (w 0) (w a) : EReal) := by
  classical
  obtain ⟨a, hamem, hmin⟩ := (Finset.univ.erase (0 : Fin K)).exists_min_image
    (fun b => pairCost F (μ 0) (μ b) (w 0) (w b)) (other_arms_nonempty hK)
  have ha : a ≠ 0 := (Finset.mem_erase.mp hamem).1
  have hmin' : ∀ b : Fin K, b ≠ 0 → pairCost F (μ 0) (μ a) (w 0) (w a) ≤
      pairCost F (μ 0) (μ b) (w 0) (w b) := fun b hb => hmin b (by simp [hb])
  refine ⟨a, ha, hmin', le_antisymm (transportCost_le_pair F μ w hμ hbest hw a ha) ?_⟩
  unfold transportCost
  apply le_iInf
  intro lam
  apply le_iInf
  intro halt
  obtain ⟨b, hb, hbound⟩ := pairCost_le_alternative F μ w hμ hbest hw lam halt
  exact EReal.coe_le_coe (hmin' b hb |>.trans hbound)

end OptimalBAI.OptProportions


open Set Filter Topology

namespace OptimalBAI.OptProportions

lemma FFun_eq {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ) (y : ℝ) :
    FFun F μ y = ∑ a ∈ Finset.univ.erase (0 : Fin K),
      allocationRatio F (μ 0) (μ a) (xFun F μ a y) := rfl

section Sorted
variable {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ) (hK : 2 ≤ K)
    (hμ : ∀ a, μ a ∈ F.M) (hμ0 : μ 1 < μ 0)
    (hsorted : ∀ a b : Fin K, 1 ≤ a → a ≤ b → μ b ≤ μ a)
include hK hμ hμ0 hsorted

lemma sorted_one_ne_zero : (1 : Fin K) ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_one'] at hv
  simp only [Fin.val_zero, Nat.mod_eq_of_lt (by omega : 1 < K)] at hv
  omega

lemma sorted_isBest : IsBest μ 0 := by
  intro a ha
  exact (hsorted 1 a le_rfl (Fin.one_le_of_ne_zero ha)).trans_lt hμ0

lemma sorted_divergence_le (a : Fin K) (ha : a ≠ 0) : F.d (μ 0) (μ 1) ≤ F.d (μ 0) (μ a) := by
  have hbest := sorted_isBest F μ hK hμ hμ0 hsorted
  exact (F.d_right_strictAnti (μ 0)).antitoneOn
    ⟨hμ a, (hbest a ha).le⟩ ⟨hμ 1, hμ0.le⟩
    (hsorted 1 a le_rfl (Fin.one_le_of_ne_zero ha))

lemma sorted_domains {y : ℝ} (hy : y ∈ Ico 0 (F.d (μ 0) (μ 1))) :
    ∀ a : Fin K, a ≠ 0 → y ∈ Ico 0 (F.d (μ 0) (μ a)) := by
  intro a ha
  exact ⟨hy.1, hy.2.trans_le (sorted_divergence_le F μ hK hμ hμ0 hsorted a ha)⟩

lemma FFun_continuousOn : ContinuousOn (FFun F μ) (Ico 0 (F.d (μ 0) (μ 1))) := by
  have hbest := sorted_isBest F μ hK hμ hμ0 hsorted
  have hs : ∀ a ≠ (0 : Fin K), Ico 0 (F.d (μ 0) (μ 1)) ⊆ Ico 0 (F.d (μ 0) (μ a)) :=
    fun a ha _ hy => sorted_domains F μ hK hμ hμ0 hsorted hy a ha
  change ContinuousOn (fun y => ∑ a ∈ Finset.univ.erase (0 : Fin K),
    allocationRatio F (μ 0) (μ a) (xFun F μ a y)) (Ico 0 (F.d (μ 0) (μ 1)))
  apply continuousOn_finsetSum
  intro a hamem
  have ha : a ≠ 0 := (Finset.mem_erase.mp hamem).1
  intro y hy
  have hcont := (xFun_continuousOn F μ hμ hbest a ha).mono (hs a ha) y hy
  have hx := xFun_mem F μ hμ hbest a ha (hs a ha hy)
  simpa only [Function.comp_def] using
    (allocationRatio_continuousAt F (hμ 0) (hμ a) (hbest a ha) hx).comp_continuousWithinAt hcont

lemma FFun_strictMono : StrictMonoOn (FFun F μ) (Ico 0 (F.d (μ 0) (μ 1))) := by
  have hbest := sorted_isBest F μ hK hμ hμ0 hsorted
  intro y hy z hz hyz
  simp only [FFun_eq]
  apply Finset.sum_lt_sum_of_nonempty (other_arms_nonempty hK)
  intro a hamem
  have ha : a ≠ 0 := (Finset.mem_erase.mp hamem).1
  have hyD := sorted_domains F μ hK hμ hμ0 hsorted hy a ha
  have hzD := sorted_domains F μ hK hμ hμ0 hsorted hz a ha
  exact allocationRatio_strictMono F (hμ 0) (hμ a) (hbest a ha)
    (xFun_mem F μ hμ hbest a ha hyD) (xFun_mem F μ hμ hbest a ha hzD)
    (xFun_strictMono F μ hμ hbest a ha hyD hzD hyz)

lemma FFun_zero : FFun F μ 0 = 0 := by
  have hbest := sorted_isBest F μ hK hμ hμ0 hsorted
  rw [FFun_eq]
  apply Finset.sum_eq_zero
  intro a hamem
  have ha : a ≠ 0 := (Finset.mem_erase.mp hamem).1
  rw [xFun_zero F μ hμ hbest a ha, allocationRatio_zero]

lemma FFun_tendsto_atTop : Tendsto (FFun F μ) (𝓝[<] (F.d (μ 0) (μ 1))) atTop := by
  have hbest := sorted_isBest F μ hK hμ hμ0 hsorted
  have h10 := sorted_one_ne_zero F μ hK hμ hμ0 hsorted
  have hDpos := F.d_pos (hμ 0) (hμ 1) (ne_of_gt hμ0)
  have hlim := (allocationRatio_tendsto F (hμ 0) (hμ 1) hμ0).comp
    (xFun_tendsto_atTop F μ hμ hbest 1 h10)
  apply tendsto_atTop_mono' (𝓝[<] (F.d (μ 0) (μ 1))) _ hlim
  filter_upwards [(eventually_gt_nhds hDpos).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with y hy0 hyD
  have hy : y ∈ Ico 0 (F.d (μ 0) (μ 1)) := ⟨hy0.le, hyD⟩
  have hsum := Finset.single_le_sum
    (s := Finset.univ.erase (0 : Fin K))
    (f := fun a => allocationRatio F (μ 0) (μ a) (xFun F μ a y))
    (fun a hamem => allocationRatio_nonneg F (hμ 0) (hμ a)
      (hbest a (Finset.mem_erase.mp hamem).1)
      (xFun_mem F μ hμ hbest a (Finset.mem_erase.mp hamem).1
        (sorted_domains F μ hK hμ hμ0 hsorted hy a (Finset.mem_erase.mp hamem).1)))
    (show (1 : Fin K) ∈ Finset.univ.erase 0 from by simp [h10])
  simpa only [FFun_eq, Function.comp_def] using hsum

lemma FFun_unique_level_one : ∃ ystar : ℝ, ystar ∈ Ico 0 (F.d (μ 0) (μ 1)) ∧
    FFun F μ ystar = 1 ∧
    (∀ y ∈ Ico 0 (F.d (μ 0) (μ 1)), FFun F μ y = 1 → y = ystar) ∧ 0 < ystar := by
  have hDpos := F.d_pos (hμ 0) (hμ 1) (ne_of_gt hμ0)
  have hlim := FFun_tendsto_atTop F μ hK hμ hμ0 hsorted
  have hev : ∀ᶠ y : ℝ in 𝓝[<] (F.d (μ 0) (μ 1)),
      0 < y ∧ y < F.d (μ 0) (μ 1) ∧ 1 < FFun F μ y := by
    filter_upwards [(eventually_gt_nhds hDpos).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin, hlim.eventually_gt_atTop 1] with y hy0 hyD hyF
    exact ⟨hy0, hyD, hyF⟩
  obtain ⟨b, hb0, hbD, hbF⟩ := hev.exists
  have hcont := (FFun_continuousOn F μ hK hμ hμ0 hsorted).mono
    (show Icc 0 b ⊆ Ico 0 (F.d (μ 0) (μ 1)) from fun _ hy => ⟨hy.1, hy.2.trans_lt hbD⟩)
  have h1 : (1 : ℝ) ∈ Icc (FFun F μ 0) (FFun F μ b) := by
    rw [FFun_zero F μ hK hμ hμ0 hsorted]
    exact ⟨zero_le_one, hbF.le⟩
  obtain ⟨ystar, hy, hyF⟩ := intermediate_value_Icc hb0.le hcont h1
  have hyD : ystar ∈ Ico 0 (F.d (μ 0) (μ 1)) := ⟨hy.1, hy.2.trans_lt hbD⟩
  refine ⟨ystar, hyD, hyF, ?_, ?_⟩
  · intro y hy hFy
    exact (FFun_strictMono F μ hK hμ hμ0 hsorted).injOn hy hyD (hFy.trans hyF.symm)
  · by_contra h
    have hy0 : ystar = 0 := le_antisymm (le_of_not_gt h) hy.1
    rw [hy0, FFun_zero F μ hK hμ hμ0 hsorted] at hyF
    norm_num at hyF

end Sorted
end OptimalBAI.OptProportions


open Set Filter Topology

namespace OptimalBAI.OptProportions

noncomputable def xSum {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ) (y : ℝ) : ℝ :=
  ∑ i, xFun F μ i y

noncomputable def normalized {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ)
    (y : ℝ) (a : Fin K) : ℝ := xFun F μ a y / xSum F μ y

lemma xFun_arm0 {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ) (y : ℝ) :
    xFun F μ 0 y = 1 := by simp [xFun]

section Normalize
variable {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0)
include hμ hbest

lemma xFun_nonneg_all {y : ℝ} (hDom : ∀ a : Fin K, a ≠ 0 → y ∈ Ico 0 (F.d (μ 0) (μ a)))
    (a : Fin K) : 0 ≤ xFun F μ a y := by
  by_cases ha : a = 0
  · subst a; simp [xFun_arm0]
  · exact xFun_mem F μ hμ hbest a ha (hDom a ha)

lemma xSum_ge_one {y : ℝ} (hDom : ∀ a : Fin K, a ≠ 0 → y ∈ Ico 0 (F.d (μ 0) (μ a))) :
    1 ≤ xSum F μ y := by
  have h := Finset.single_le_sum (f := fun a => xFun F μ a y)
    (fun a _ => xFun_nonneg_all F μ hμ hbest hDom a) (Finset.mem_univ (0 : Fin K))
  simpa only [xFun_arm0, xSum] using h

lemma xSum_pos {y : ℝ} (hDom : ∀ a : Fin K, a ≠ 0 → y ∈ Ico 0 (F.d (μ 0) (μ a))) :
    0 < xSum F μ y := lt_of_lt_of_le zero_lt_one (xSum_ge_one F μ hμ hbest hDom)

lemma normalized_simplex {y : ℝ} (hDom : ∀ a : Fin K, a ≠ 0 → y ∈ Ico 0 (F.d (μ 0) (μ a))) :
    normalized F μ y ∈ simplex K := by
  have hS := xSum_pos F μ hμ hbest hDom
  constructor
  · intro a
    exact div_nonneg (xFun_nonneg_all F μ hμ hbest hDom a) hS.le
  · simp only [normalized, ← Finset.sum_div]
    change xSum F μ y / xSum F μ y = 1
    exact div_self hS.ne'

omit hμ hbest in
lemma normalized_arm0 {y : ℝ} : normalized F μ y 0 = 1 / xSum F μ y := by
  simp only [normalized, xFun_arm0]

lemma normalized_ratio {y : ℝ} (hDom : ∀ a : Fin K, a ≠ 0 → y ∈ Ico 0 (F.d (μ 0) (μ a)))
    (a : Fin K) : normalized F μ y a / normalized F μ y 0 = xFun F μ a y := by
  have hS := (xSum_pos F μ hμ hbest hDom).ne'
  rw [normalized_arm0]
  unfold normalized
  field_simp

lemma normalized_pairCost {y : ℝ} (hDom : ∀ a : Fin K, a ≠ 0 → y ∈ Ico 0 (F.d (μ 0) (μ a)))
    (a : Fin K) (ha : a ≠ 0) :
    pairCost F (μ 0) (μ a) (normalized F μ y 0) (normalized F μ y a) = y / xSum F μ y := by
  have hw := normalized_simplex F μ hμ hbest hDom
  have hp : 0 < normalized F μ y 0 := by rw [normalized_arm0]; exact one_div_pos.mpr (xSum_pos F μ hμ hbest hDom)
  rw [pairCost_ratio F μ a hp (hw.1 a), normalized_ratio F μ hμ hbest hDom a,
    gFun_xFun F μ hμ hbest a ha (hDom a ha), normalized_arm0]
  ring

lemma normalized_transportCost (hK : 2 ≤ K) {y : ℝ}
    (hDom : ∀ a : Fin K, a ≠ 0 → y ∈ Ico 0 (F.d (μ 0) (μ a))) :
    transportCost F μ (normalized F μ y) = ((y / xSum F μ y : ℝ) : EReal) := by
  obtain ⟨a, ha, hmin, hcost⟩ := transportCost_min_pair F μ hK hμ hbest (normalized F μ y)
    (normalized_simplex F μ hμ hbest hDom)
  rw [hcost, normalized_pairCost F μ hμ hbest hDom a ha]

end Normalize

noncomputable def uniform (K : ℕ) : Fin K → ℝ := fun _ => 1 / (K : ℝ)

lemma uniform_simplex {K : ℕ} (hK : 0 < K) : uniform K ∈ simplex K := by
  have hKr : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  constructor
  · intro i; exact (one_div_pos.mpr hKr).le
  · simp only [uniform, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

lemma uniform_transportCost_pos {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ)
    (hK : 2 ≤ K) (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) :
    (0 : EReal) < transportCost F μ (uniform K) := by
  have hKp : 0 < K := by omega
  have hp : 0 < 1 / (K : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hKp)
  obtain ⟨a, ha, hmin, hcost⟩ := transportCost_min_pair F μ hK hμ hbest (uniform K) (uniform_simplex hKp)
  rw [hcost]
  have h := pairCost_pos F (hμ 0) (hμ a) (hbest a ha) hp hp
  exact_mod_cast h

lemma optimal_transportCost_pos {K : ℕ} [NeZero K] (F : ExpFamily) (μ w : Fin K → ℝ)
    (hK : 2 ≤ K) (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (hw : IsOptimalProportion F μ w) :
    (0 : EReal) < transportCost F μ w :=
  (uniform_transportCost_pos F μ hK hμ hbest).trans_le
    (hw.2 (uniform K) (uniform_simplex (by omega)))

lemma optimal_weights_pos {K : ℕ} [NeZero K] (F : ExpFamily) (μ w : Fin K → ℝ)
    (hK : 2 ≤ K) (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (hw : IsOptimalProportion F μ w) :
    ∀ i, 0 < w i := by
  have hcost := optimal_transportCost_pos F μ w hK hμ hbest hw
  intro i
  by_contra hi
  have hwi : w i = 0 := le_antisymm (le_of_not_gt hi) (hw.1.1 i)
  by_cases hi0 : i = 0
  · subst i
    obtain ⟨a, hamem⟩ := other_arms_nonempty hK
    have ha : a ≠ 0 := (Finset.mem_erase.mp hamem).1
    have hbound := transportCost_le_pair F μ w hμ hbest hw.1 a ha
    rw [hwi, pairCost_left_zero, EReal.coe_zero] at hbound
    exact (not_le_of_gt hcost) hbound
  · have hbound := transportCost_le_pair F μ w hμ hbest hw.1 i hi0
    rw [hwi, pairCost_right_zero F _ _ (hw.1.1 0), EReal.coe_zero] at hbound
    exact (not_le_of_gt hcost) hbound

end OptimalBAI.OptProportions


open Set Filter Topology

namespace OptimalBAI.OptProportions

noncomputable def objective {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ) (y : ℝ) : ℝ :=
  y / xSum F μ y

lemma xSum_eq {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ) (y : ℝ) :
    xSum F μ y = 1 + ∑ a ∈ Finset.univ.erase (0 : Fin K), xFun F μ a y := by
  have h := Finset.add_sum_erase Finset.univ (fun a => xFun F μ a y) (Finset.mem_univ (0 : Fin K))
  simpa only [xSum, xFun_arm0] using h.symm

section Sorted
variable {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ) (hK : 2 ≤ K)
    (hμ : ∀ a, μ a ∈ F.M) (hμ0 : μ 1 < μ 0)
    (hsorted : ∀ a b : Fin K, 1 ≤ a → a ≤ b → μ b ≤ μ a)
include hK hμ hμ0 hsorted

lemma xSum_continuousOn : ContinuousOn (xSum F μ) (Ico 0 (F.d (μ 0) (μ 1))) := by
  have hbest := sorted_isBest F μ hK hμ hμ0 hsorted
  unfold xSum
  apply continuousOn_finsetSum
  intro a hamem
  by_cases ha : a = 0
  · subst a
    convert (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Ico 0 (F.d (μ 0) (μ 1)))) using 1
    funext y
    exact xFun_arm0 F μ y
  · exact (xFun_continuousOn F μ hμ hbest a ha).mono
      (fun _ hy => sorted_domains F μ hK hμ hμ0 hsorted hy a ha)

lemma objective_continuousOn : ContinuousOn (objective F μ) (Ico 0 (F.d (μ 0) (μ 1))) := by
  have hbest := sorted_isBest F μ hK hμ hμ0 hsorted
  apply continuousOn_id.div (xSum_continuousOn F μ hK hμ hμ0 hsorted)
  intro y hy
  exact (xSum_pos F μ hμ hbest (sorted_domains F μ hK hμ hμ0 hsorted hy)).ne'

lemma xSum_hasDerivAt {y : ℝ} (hy0 : 0 < y) (hyD : y < F.d (μ 0) (μ 1)) :
    HasDerivAt (xSum F μ)
      (∑ a ∈ Finset.univ.erase (0 : Fin K),
        (F.d (μ a) (mix (μ 0) (μ a) (xFun F μ a y)))⁻¹) y := by
  have hbest := sorted_isBest F μ hK hμ hμ0 hsorted
  have hDom := sorted_domains F μ hK hμ hμ0 hsorted ⟨hy0.le, hyD⟩
  have hsum : HasDerivAt (fun z => ∑ a ∈ Finset.univ.erase (0 : Fin K), xFun F μ a z)
      (∑ a ∈ Finset.univ.erase (0 : Fin K),
        (F.d (μ a) (mix (μ 0) (μ a) (xFun F μ a y)))⁻¹) y := by
    apply HasDerivAt.fun_sum
    intro a hamem
    have ha : a ≠ 0 := (Finset.mem_erase.mp hamem).1
    exact xFun_hasDerivAt F μ hμ hbest a ha hy0 (hDom a ha).2
  convert hsum.const_add 1 using 1 <;> first | rfl | (funext z; exact xSum_eq F μ z)

lemma inverse_cost_identity {y : ℝ} (hy : y ∈ Ico 0 (F.d (μ 0) (μ 1)))
    (a : Fin K) (ha : a ≠ 0) :
    y * (F.d (μ a) (mix (μ 0) (μ a) (xFun F μ a y)))⁻¹ =
      xFun F μ a y + allocationRatio F (μ 0) (μ a) (xFun F μ a y) := by
  have hbest := sorted_isBest F μ hK hμ hμ0 hsorted
  have hDom := sorted_domains F μ hK hμ hμ0 hsorted hy a ha
  have hx := xFun_mem F μ hμ hbest a ha hDom
  have hm := mix_mem F (hμ 0) (hμ a) (hbest a ha) hx
  have hden : F.d (μ a) (mix (μ 0) (μ a) (xFun F μ a y)) ≠ 0 :=
    ne_of_gt (F.d_pos (hμ a) hm (ne_of_lt (mix_bounds (hbest a ha) hx).1))
  have h := gFun_xFun F μ hμ hbest a ha hDom
  rw [gFun_eq F μ a _ (by linarith [show 0 ≤ xFun F μ a y from hx])] at h
  unfold allocationRatio
  field_simp
  nlinarith

lemma objective_numerator {y : ℝ} (hy : y ∈ Ico 0 (F.d (μ 0) (μ 1))) :
    xSum F μ y - y * (∑ a ∈ Finset.univ.erase (0 : Fin K),
      (F.d (μ a) (mix (μ 0) (μ a) (xFun F μ a y)))⁻¹) = 1 - FFun F μ y := by
  have hsum : (∑ a ∈ Finset.univ.erase (0 : Fin K),
      y * (F.d (μ a) (mix (μ 0) (μ a) (xFun F μ a y)))⁻¹) =
      ∑ a ∈ Finset.univ.erase (0 : Fin K),
        (xFun F μ a y + allocationRatio F (μ 0) (μ a) (xFun F μ a y)) := by
    apply Finset.sum_congr rfl
    intro a hamem
    exact inverse_cost_identity F μ hK hμ hμ0 hsorted hy a (Finset.mem_erase.mp hamem).1
  rw [xSum_eq, Finset.mul_sum, hsum, Finset.sum_add_distrib, ← FFun_eq]
  ring

lemma objective_hasDerivAt {y : ℝ} (hy0 : 0 < y) (hyD : y < F.d (μ 0) (μ 1)) :
    HasDerivAt (objective F μ) ((1 - FFun F μ y) / (xSum F μ y)^2) y := by
  have hbest := sorted_isBest F μ hK hμ hμ0 hsorted
  have hS := xSum_pos F μ hμ hbest (sorted_domains F μ hK hμ hμ0 hsorted ⟨hy0.le, hyD⟩)
  have hx := xSum_hasDerivAt F μ hK hμ hμ0 hsorted hy0 hyD
  have h := (hasDerivAt_id y).div hx hS.ne'
  have hnum := objective_numerator F μ hK hμ hμ0 hsorted ⟨hy0.le, hyD⟩
  convert h using 1 <;> first | rfl | (simp only [one_mul, id_eq]; rw [hnum])

lemma objective_strictMono_before {ystar : ℝ} (hy : ystar ∈ Ico 0 (F.d (μ 0) (μ 1)))
    (hyF : FFun F μ ystar = 1) : StrictMonoOn (objective F μ) (Icc 0 ystar) := by
  have hbest := sorted_isBest F μ hK hμ hμ0 hsorted
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 ystar)
    ((objective_continuousOn F μ hK hμ hμ0 hsorted).mono
      (fun _ hx => ⟨hx.1, hx.2.trans_lt hy.2⟩))
  intro z hz
  have hz' : z ∈ Ioo 0 ystar := by simpa only [interior_Icc] using hz
  have hzD : z ∈ Ico 0 (F.d (μ 0) (μ 1)) := ⟨hz'.1.le, hz'.2.trans hy.2⟩
  have hF : FFun F μ z < 1 := by
    simpa only [hyF] using FFun_strictMono F μ hK hμ hμ0 hsorted hzD hy hz'.2
  rw [(objective_hasDerivAt F μ hK hμ hμ0 hsorted hz'.1 hzD.2).deriv]
  exact div_pos (sub_pos.mpr hF) (sq_pos_of_pos (xSum_pos F μ hμ hbest
    (sorted_domains F μ hK hμ hμ0 hsorted hzD)))

lemma objective_strictAnti_after {ystar : ℝ} (hy : ystar ∈ Ico 0 (F.d (μ 0) (μ 1)))
    (hyF : FFun F μ ystar = 1) : StrictAntiOn (objective F μ) (Ico ystar (F.d (μ 0) (μ 1))) := by
  have hbest := sorted_isBest F μ hK hμ hμ0 hsorted
  apply strictAntiOn_of_deriv_neg (convex_Ico ystar _)
    ((objective_continuousOn F μ hK hμ hμ0 hsorted).mono
      (fun _ hx => ⟨hy.1.trans hx.1, hx.2⟩))
  intro z hz
  have hz' : z ∈ Ioo ystar (F.d (μ 0) (μ 1)) := by simpa only [interior_Ico] using hz
  have hz0 : 0 < z := hy.1.trans_lt hz'.1
  have hzD : z ∈ Ico 0 (F.d (μ 0) (μ 1)) := ⟨hz0.le, hz'.2⟩
  have hF : 1 < FFun F μ z := by
    simpa only [hyF] using FFun_strictMono F μ hK hμ hμ0 hsorted hy hzD hz'.1
  rw [(objective_hasDerivAt F μ hK hμ hμ0 hsorted hz0 hz'.2).deriv]
  exact div_neg_of_neg_of_pos (sub_neg.mpr hF) (sq_pos_of_pos (xSum_pos F μ hμ hbest
    (sorted_domains F μ hK hμ hμ0 hsorted hzD)))

lemma objective_unique_max {ystar : ℝ} (hy : ystar ∈ Ico 0 (F.d (μ 0) (μ 1)))
    (hyF : FFun F μ ystar = 1) {y : ℝ} (hyDom : y ∈ Ico 0 (F.d (μ 0) (μ 1)))
    (hne : y ≠ ystar) : objective F μ y < objective F μ ystar := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact objective_strictMono_before F μ hK hμ hμ0 hsorted hy hyF
      ⟨hyDom.1, hlt.le⟩ ⟨hy.1, le_rfl⟩ hlt
  · exact objective_strictAnti_after F μ hK hμ hμ0 hsorted hy hyF
      ⟨le_rfl, hy.2⟩ ⟨hgt.le, hyDom.2⟩ hgt

end Sorted
end OptimalBAI.OptProportions


open Set Filter Topology

namespace OptimalBAI.OptProportions

lemma transportCost_min_ratio {K : ℕ} [NeZero K] (F : ExpFamily) (μ w : Fin K → ℝ)
    (hK : 2 ≤ K) (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (hw : w ∈ simplex K)
    (hw0 : 0 < w 0) :
    ∃ a : Fin K, a ≠ 0 ∧ transportCost F μ w = ((w 0 * gFun F μ a (w a / w 0) : ℝ) : EReal) ∧
      ∀ b : Fin K, b ≠ 0 → gFun F μ a (w a / w 0) ≤ gFun F μ b (w b / w 0) := by
  obtain ⟨a, ha, hmin, hcost⟩ := transportCost_min_pair F μ hK hμ hbest w hw
  refine ⟨a, ha, ?_, ?_⟩
  · simpa only [pairCost_ratio F μ a hw0 (hw.1 a)] using hcost
  · intro b hb
    have h := hmin b hb
    rw [pairCost_ratio F μ a hw0 (hw.1 a), pairCost_ratio F μ b hw0 (hw.1 b)] at h
    exact (mul_le_mul_iff_right₀ hw0).mp (by simpa only [mul_comm] using h)

lemma gFun_nonneg {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (a : Fin K) (ha : a ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ gFun F μ a x := by
  simpa only [gFun_zero] using (gFun_strictMono F μ hμ hbest a ha).monotoneOn
    (show (0 : ℝ) ∈ Ici 0 from by simp) hx hx

lemma min_ratio_domains {K : ℕ} [NeZero K] (F : ExpFamily) (μ w : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (hw : w ∈ simplex K) (hw0 : 0 < w 0)
    (a : Fin K) (ha : a ≠ 0)
    (hmin : ∀ b : Fin K, b ≠ 0 → gFun F μ a (w a / w 0) ≤ gFun F μ b (w b / w 0)) :
    ∀ b : Fin K, b ≠ 0 → gFun F μ a (w a / w 0) ∈ Ico 0 (F.d (μ 0) (μ b)) := by
  intro b hb
  refine ⟨gFun_nonneg F μ hμ hbest a ha (div_nonneg (hw.1 a) hw0.le), ?_⟩
  exact (hmin b hb).trans_lt
    (gFun_lt_limit F μ hμ hbest b hb (div_nonneg (hw.1 b) hw0.le))

lemma clamp_le_ratio {K : ℕ} [NeZero K] (F : ExpFamily) (μ w : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (hw : w ∈ simplex K) (hw0 : 0 < w 0)
    {y : ℝ} (hDom : ∀ a : Fin K, a ≠ 0 → y ∈ Ico 0 (F.d (μ 0) (μ a)))
    (hmin : ∀ a : Fin K, a ≠ 0 → y ≤ gFun F μ a (w a / w 0)) (a : Fin K) :
    xFun F μ a y ≤ w a / w 0 := by
  by_cases ha : a = 0
  · subst a
    rw [xFun_arm0, div_self hw0.ne']
  · have hx : 0 ≤ w a / w 0 := div_nonneg (hw.1 a) hw0.le
    have hgDom : gFun F μ a (w a / w 0) ∈ Ico 0 (F.d (μ 0) (μ a)) :=
      ⟨gFun_nonneg F μ hμ hbest a ha hx, gFun_lt_limit F μ hμ hbest a ha hx⟩
    have h := (xFun_strictMono F μ hμ hbest a ha).monotoneOn (hDom a ha) hgDom (hmin a ha)
    simpa only [xFun_gFun F μ hμ hbest a ha hx] using h

lemma clamp_lt_ratio {K : ℕ} [NeZero K] (F : ExpFamily) (μ w : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (hw : w ∈ simplex K) (hw0 : 0 < w 0)
    {y : ℝ} (hDom : ∀ a : Fin K, a ≠ 0 → y ∈ Ico 0 (F.d (μ 0) (μ a)))
    (a : Fin K) (ha : a ≠ 0) (hlt : y < gFun F μ a (w a / w 0)) :
    xFun F μ a y < w a / w 0 := by
  have hx : 0 ≤ w a / w 0 := div_nonneg (hw.1 a) hw0.le
  have hgDom : gFun F μ a (w a / w 0) ∈ Ico 0 (F.d (μ 0) (μ a)) :=
    ⟨gFun_nonneg F μ hμ hbest a ha hx, gFun_lt_limit F μ hμ hbest a ha hx⟩
  have h := xFun_strictMono F μ hμ hbest a ha (hDom a ha) hgDom hlt
  simpa only [xFun_gFun F μ hμ hbest a ha hx] using h

lemma clamp_sum_lt {K : ℕ} [NeZero K] (F : ExpFamily) (μ w : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (hw : w ∈ simplex K) (hw0 : 0 < w 0)
    {y : ℝ} (hDom : ∀ a : Fin K, a ≠ 0 → y ∈ Ico 0 (F.d (μ 0) (μ a)))
    (hmin : ∀ a : Fin K, a ≠ 0 → y ≤ gFun F μ a (w a / w 0))
    (b : Fin K) (hb : b ≠ 0) (hlt : y < gFun F μ b (w b / w 0)) :
    xSum F μ y < 1 / w 0 := by
  have hsum := Finset.sum_lt_sum
    (fun a (_ : a ∈ (Finset.univ : Finset (Fin K))) => clamp_le_ratio F μ w hμ hbest hw hw0 hDom hmin a)
    ⟨b, Finset.mem_univ b, clamp_lt_ratio F μ w hμ hbest hw hw0 hDom b hb hlt⟩
  simpa only [xSum, ← Finset.sum_div, hw.2] using hsum

lemma optimal_ratios_equal {K : ℕ} [NeZero K] (F : ExpFamily) (μ w : Fin K → ℝ)
    (hK : 2 ≤ K) (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (hw : IsOptimalProportion F μ w)
    (a : Fin K) (ha : a ≠ 0)
    (hcost : transportCost F μ w = ((w 0 * gFun F μ a (w a / w 0) : ℝ) : EReal))
    (hmin : ∀ b : Fin K, b ≠ 0 → gFun F μ a (w a / w 0) ≤ gFun F μ b (w b / w 0)) :
    ∀ b : Fin K, b ≠ 0 → gFun F μ a (w a / w 0) = gFun F μ b (w b / w 0) := by
  have hwpos := optimal_weights_pos F μ w hK hμ hbest hw
  have hDom := min_ratio_domains F μ w hμ hbest hw.1 (hwpos 0) a ha hmin
  let y := gFun F μ a (w a / w 0)
  have hy : 0 < y := by
    have hx : 0 < w a / w 0 := div_pos (hwpos a) (hwpos 0)
    have h := gFun_strictMono F μ hμ hbest a ha (show (0 : ℝ) ∈ Ici 0 from by simp) hx.le hx
    simpa only [gFun_zero] using h
  intro b hb
  by_contra hne
  have hlt : y < gFun F μ b (w b / w 0) := lt_of_le_of_ne (hmin b hb) hne
  have hSlt : xSum F μ y < 1 / w 0 := clamp_sum_lt F μ w hμ hbest hw.1 (hwpos 0) hDom hmin b hb hlt
  have hSpos := xSum_pos F μ hμ hbest hDom
  have hnorm := normalized_simplex F μ hμ hbest hDom
  have hnormcost := normalized_transportCost F μ hμ hbest hK hDom
  have hopt := hw.2 (normalized F μ y) hnorm
  rw [hnormcost, hcost, EReal.coe_le_coe_iff] at hopt
  have hineq : y ≤ w 0 * y * xSum F μ y := (div_le_iff₀ hSpos).mp hopt
  have hSprod : w 0 * xSum F μ y < 1 := by
    have h := (lt_div_iff₀ (hwpos 0)).mp hSlt
    nlinarith
  have hcontra : 0 < y * (1 - w 0 * xSum F μ y) := mul_pos hy (sub_pos.mpr hSprod)
  nlinarith

lemma optimal_pair_costs_equal {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ)
    (hK : 2 ≤ K) (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0)
    (w : Fin K → ℝ) (hw : IsOptimalProportion F μ w)
    (a b : Fin K) (ha : a ≠ 0) (hb : b ≠ 0) :
    pairCost F (μ 0) (μ a) (w 0) (w a) = pairCost F (μ 0) (μ b) (w 0) (w b) := by
  have hw0 := optimal_weights_pos F μ w hK hμ hbest hw 0
  obtain ⟨c, hc, hcost, hmin⟩ := transportCost_min_ratio F μ w hK hμ hbest hw.1 hw0
  have heq := optimal_ratios_equal F μ w hK hμ hbest hw c hc hcost hmin
  rw [pairCost_ratio F μ a hw0 (hw.1.1 a), pairCost_ratio F μ b hw0 (hw.1.1 b),
    ← heq a ha, ← heq b hb]

end OptimalBAI.OptProportions


open Set Filter Topology

namespace OptimalBAI.OptProportions

lemma transportCost_nonneg {K : ℕ} [NeZero K] (F : ExpFamily) (μ w : Fin K → ℝ)
    (hK : 2 ≤ K) (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (hw : w ∈ simplex K) :
    (0 : EReal) ≤ transportCost F μ w := by
  obtain ⟨a, ha, hmin, hcost⟩ := transportCost_min_pair F μ hK hμ hbest w hw
  rw [hcost]
  exact_mod_cast pairCost_nonneg F (hμ 0) (hμ a) (hbest a ha).le (hw.1 0) (hw.1 a)

lemma transportCost_best_weight_zero {K : ℕ} [NeZero K] (F : ExpFamily) (μ w : Fin K → ℝ)
    (hK : 2 ≤ K) (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (hw : w ∈ simplex K)
    (hw0 : w 0 = 0) : transportCost F μ w = 0 := by
  obtain ⟨a, hamem⟩ := other_arms_nonempty hK
  have ha : a ≠ 0 := (Finset.mem_erase.mp hamem).1
  have h := transportCost_le_pair F μ w hμ hbest hw a ha
  rw [hw0, pairCost_left_zero, EReal.coe_zero] at h
  exact le_antisymm h (transportCost_nonneg F μ w hK hμ hbest hw)

lemma clamp_objective_bound {K : ℕ} [NeZero K] (F : ExpFamily) (μ w : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (hw : w ∈ simplex K) (hw0 : 0 < w 0)
    {y : ℝ} (hy0 : 0 ≤ y) (hDom : ∀ a : Fin K, a ≠ 0 → y ∈ Ico 0 (F.d (μ 0) (μ a)))
    (hmin : ∀ a : Fin K, a ≠ 0 → y ≤ gFun F μ a (w a / w 0)) :
    w 0 * y ≤ objective F μ y := by
  have hsum := Finset.sum_le_sum
    (fun a (_ : a ∈ (Finset.univ : Finset (Fin K))) => clamp_le_ratio F μ w hμ hbest hw hw0 hDom hmin a)
  have hSle : xSum F μ y ≤ 1 / w 0 := by
    simpa only [xSum, ← Finset.sum_div, hw.2] using hsum
  have hSpos := xSum_pos F μ hμ hbest hDom
  have hSprod : w 0 * xSum F μ y ≤ 1 := by
    have h := (le_div_iff₀ hw0).mp hSle
    nlinarith
  unfold objective
  apply (le_div_iff₀ hSpos).mpr
  have hprod := mul_nonneg hy0 (sub_nonneg.mpr hSprod)
  nlinarith

lemma optimal_is_normalized {K : ℕ} [NeZero K] (F : ExpFamily) (μ w : Fin K → ℝ)
    (hK : 2 ≤ K) (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (hw : IsOptimalProportion F μ w) :
    ∃ y : ℝ, (∀ a : Fin K, a ≠ 0 → y ∈ Ico 0 (F.d (μ 0) (μ a))) ∧ w = normalized F μ y := by
  have hw0 := optimal_weights_pos F μ w hK hμ hbest hw 0
  obtain ⟨a, ha, hcost, hmin⟩ := transportCost_min_ratio F μ w hK hμ hbest hw.1 hw0
  let y := gFun F μ a (w a / w 0)
  have hDom := min_ratio_domains F μ w hμ hbest hw.1 hw0 a ha hmin
  have heq := optimal_ratios_equal F μ w hK hμ hbest hw a ha hcost hmin
  have hx : ∀ b : Fin K, xFun F μ b y = w b / w 0 := by
    intro b
    by_cases hb : b = 0
    · subst b; rw [xFun_arm0, div_self hw0.ne']
    · change xFun F μ b (gFun F μ a (w a / w 0)) = _
      rw [heq b hb, xFun_gFun F μ hμ hbest b hb (div_nonneg (hw.1.1 b) hw0.le)]
  have hS : xSum F μ y = 1 / w 0 := by
    unfold xSum
    simp_rw [hx]
    rw [← Finset.sum_div, hw.1.2]
  refine ⟨y, hDom, funext fun b => ?_⟩
  unfold normalized
  rw [hx, hS]
  field_simp

section Sorted
variable {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ) (hK : 2 ≤ K)
    (hμ : ∀ a, μ a ∈ F.M) (hμ0 : μ 1 < μ 0)
    (hsorted : ∀ a b : Fin K, 1 ≤ a → a ≤ b → μ b ≤ μ a)
include hK hμ hμ0 hsorted

lemma all_costs_le_objective_max {ystar : ℝ} (hy : ystar ∈ Ico 0 (F.d (μ 0) (μ 1)))
    (hyF : FFun F μ ystar = 1) (w : Fin K → ℝ) (hw : w ∈ simplex K) :
    transportCost F μ w ≤ (objective F μ ystar : EReal) := by
  have hbest := sorted_isBest F μ hK hμ hμ0 hsorted
  have h10 := sorted_one_ne_zero F μ hK hμ hμ0 hsorted
  by_cases hwz : w 0 = 0
  · rw [transportCost_best_weight_zero F μ w hK hμ hbest hw hwz]
    have hS := xSum_pos F μ hμ hbest (sorted_domains F μ hK hμ hμ0 hsorted hy)
    have hG : 0 ≤ objective F μ ystar := div_nonneg hy.1 hS.le
    exact_mod_cast hG
  · have hw0 : 0 < w 0 := lt_of_le_of_ne (hw.1 0) (Ne.symm hwz)
    obtain ⟨a, ha, hcost, hmin⟩ := transportCost_min_ratio F μ w hK hμ hbest hw hw0
    let y := gFun F μ a (w a / w 0)
    have hDom := min_ratio_domains F μ w hμ hbest hw hw0 a ha hmin
    have hyD : y ∈ Ico 0 (F.d (μ 0) (μ 1)) := hDom 1 h10
    have hbound : w 0 * y ≤ objective F μ y :=
      clamp_objective_bound F μ w hμ hbest hw hw0 hyD.1 hDom hmin
    have hmax : objective F μ y ≤ objective F μ ystar := by
      by_cases heq : y = ystar
      · rw [heq]
      · exact (objective_unique_max F μ hK hμ hμ0 hsorted hy hyF hyD heq).le
    rw [hcost]
    exact EReal.coe_le_coe (hbound.trans hmax)

lemma normalized_isOptimal {ystar : ℝ} (hy : ystar ∈ Ico 0 (F.d (μ 0) (μ 1)))
    (hyF : FFun F μ ystar = 1) : IsOptimalProportion F μ (normalized F μ ystar) := by
  have hbest := sorted_isBest F μ hK hμ hμ0 hsorted
  have hDom := sorted_domains F μ hK hμ hμ0 hsorted hy
  refine ⟨normalized_simplex F μ hμ hbest hDom, ?_⟩
  intro w hw
  rw [normalized_transportCost F μ hμ hbest hK hDom]
  exact all_costs_le_objective_max F μ hK hμ hμ0 hsorted hy hyF w hw

lemma optimal_iff_normalized {ystar : ℝ} (hy : ystar ∈ Ico 0 (F.d (μ 0) (μ 1)))
    (hyF : FFun F μ ystar = 1) (w : Fin K → ℝ) :
    IsOptimalProportion F μ w ↔ w = normalized F μ ystar := by
  constructor
  · intro hw
    have hbest := sorted_isBest F μ hK hμ hμ0 hsorted
    have h10 := sorted_one_ne_zero F μ hK hμ hμ0 hsorted
    obtain ⟨y, hDom, hwNorm⟩ := optimal_is_normalized F μ w hK hμ hbest hw
    have hyD : y ∈ Ico 0 (F.d (μ 0) (μ 1)) := hDom 1 h10
    have hstarDom := sorted_domains F μ hK hμ hμ0 hsorted hy
    have hopt := hw.2 (normalized F μ ystar) (normalized_simplex F μ hμ hbest hstarDom)
    rw [hwNorm, normalized_transportCost F μ hμ hbest hK hDom,
      normalized_transportCost F μ hμ hbest hK hstarDom, EReal.coe_le_coe_iff] at hopt
    have heq : y = ystar := by
      by_contra hne
      exact (not_le_of_gt (objective_unique_max F μ hK hμ hμ0 hsorted hy hyF hyD hne)) hopt
    simpa only [heq] using hwNorm
  · intro hw
    rw [hw]
    exact normalized_isOptimal F μ hK hμ hμ0 hsorted hy hyF

end Sorted

end OptimalBAI.OptProportions


open Set Filter Topology
namespace OptimalBAI.TrackStop

def ExpFamily.toAllocationFamily (F : ExpFamily) : OptimalBAI.OptProportions.ExpFamily where
  ξ := F.ξ
  Θ := F.Θ
  b := F.b
  isOpen_Θ := F.isOpen_Θ
  ordConnected_Θ := F.ordConnected_Θ
  nonempty_Θ := F.nonempty_Θ
  isNormalized := F.isNormalized
  contDiff := F.contDiff
  deriv2_pos := F.deriv2_pos

lemma ExpFamily.bridge_mean (F : ExpFamily) : F.toAllocationFamily.M=F.M := rfl
lemma ExpFamily.bridge_d (F : ExpFamily) : F.toAllocationFamily.d=F.d := rfl

lemma bridge_optimal {K : ℕ} (F : ExpFamily) (μ w : Fin K → ℝ) :
    OptimalBAI.OptProportions.IsOptimalProportion F.toAllocationFamily μ w ↔
      IsOptimalProportion F μ w := Iff.rfl

lemma simplex_reindex {K : ℕ} (e : Equiv.Perm (Fin K)) (w : Fin K → ℝ) :
    w ∘ e ∈ simplex K ↔ w ∈ simplex K := by
  constructor
  · rintro ⟨hpos,hsum⟩
    refine ⟨fun i => ?_,?_⟩
    · simpa using hpos (e.symm i)
    · simpa only [Function.comp_def] using (Equiv.sum_comp e w).symm.trans hsum
  · rintro ⟨hpos,hsum⟩
    refine ⟨fun i => hpos (e i),?_⟩
    exact (Equiv.sum_comp e w).trans hsum

lemma isBest_reindex {K : ℕ} (e : Equiv.Perm (Fin K)) (μ : Fin K → ℝ) (a : Fin K) :
    IsBest (μ ∘ e) a ↔ IsBest μ (e a) := by
  constructor
  · intro h i hi
    simpa only [Function.comp_def,e.apply_symm_apply] using
      h (e.symm i) (fun he => hi (by simpa [he] using (e.apply_symm_apply i).symm))
  · intro h i hi
    exact h (e i) (fun he => hi (e.injective he))

lemma bestMeans_reindex {K : ℕ} (e : Equiv.Perm (Fin K)) (μ : Fin K → ℝ) (F : ExpFamily) :
    μ ∘ e ∈ bestArmMeans F K ↔ μ ∈ bestArmMeans F K := by
  constructor
  · rintro ⟨hm,a,ha⟩
    refine ⟨fun i => ?_,e a,(isBest_reindex e μ a).mp ha⟩
    simpa using hm (e.symm i)
  · rintro ⟨hm,a,ha⟩
    exact ⟨fun i => hm (e i),e.symm a,(isBest_reindex e μ (e.symm a)).mpr (by simpa)⟩

lemma alt_reindex {K : ℕ} (e : Equiv.Perm (Fin K)) (F : ExpFamily) (μ lam : Fin K → ℝ) :
    lam ∘ e ∈ Alt F (μ ∘ e) ↔ lam ∈ Alt F μ := by
  constructor
  · rintro ⟨hm,hbad⟩
    refine ⟨(bestMeans_reindex e lam F).mp hm,?_⟩
    intro a ha hμ
    exact hbad (e.symm a) ((isBest_reindex e lam _).mpr (by simpa))
      ((isBest_reindex e μ _).mpr (by simpa))
  · rintro ⟨hm,hbad⟩
    refine ⟨(bestMeans_reindex e lam F).mpr hm,?_⟩
    intro a ha hμ
    exact hbad (e a) ((isBest_reindex e lam a).mp ha) ((isBest_reindex e μ a).mp hμ)

lemma transportCost_reindex {K : ℕ} (e : Equiv.Perm (Fin K)) (F : ExpFamily) (μ w : Fin K → ℝ) :
    transportCost F (μ ∘ e) (w ∘ e)=transportCost F μ w := by
  let E : (Fin K → ℝ) ≃ (Fin K → ℝ) :=
    { toFun := fun f => f ∘ e
      invFun := fun f => f ∘ e.symm
      left_inv := fun f => by funext i; simp
      right_inv := fun f => by funext i; simp }
  unfold transportCost
  calc
    _ = ⨅ lam : Fin K → ℝ, ⨅ _ : E lam ∈ Alt F (μ ∘ e),
        ((∑ a, (w ∘ e) a * F.d ((μ ∘ e) a) (E lam a) : ℝ) : EReal) :=
      E.iInf_comp.symm
    _ = _ := by
      apply iInf_congr
      intro lam
      change (⨅ _ : lam ∘ e ∈ Alt F (μ ∘ e),
        ((∑ a, w (e a) * F.d (μ (e a)) (lam (e a)) : ℝ) : EReal)) = _
      rw [alt_reindex]
      apply iInf_congr
      intro h
      congr 1
      exact Equiv.sum_comp e (fun a => w a * F.d (μ a) (lam a))

lemma optimal_reindex {K : ℕ} (e : Equiv.Perm (Fin K)) (F : ExpFamily) (μ w : Fin K → ℝ) :
    IsOptimalProportion F (μ ∘ e) (w ∘ e) ↔ IsOptimalProportion F μ w := by
  constructor
  · rintro ⟨hw,hopt⟩
    refine ⟨(simplex_reindex e w).mp hw,?_⟩
    intro v hv
    simpa only [transportCost_reindex] using hopt (v ∘ e) ((simplex_reindex e v).mpr hv)
  · rintro ⟨hw,hopt⟩
    refine ⟨(simplex_reindex e w).mpr hw,?_⟩
    intro v hv
    have hh := hopt (v ∘ e.symm) ((simplex_reindex e.symm v).mpr hv)
    have he : (v ∘ e.symm) ∘ e=v := by funext i; simp
    rw [← transportCost_reindex e F μ (v ∘ e.symm),he,← transportCost_reindex e F μ w] at hh
    exact hh

end OptimalBAI.TrackStop


open MeasureTheory BanditAlgorithm Filter Topology
set_option maxHeartbeats 1500000
namespace OptimalBAI.TrackStop

lemma rewardSum_eq_count_mean {K : ℕ} (a : Fin K) (n : ℕ)
    (ω : ℕ → Fin K × ℝ) (hN : 0<trajPullCount a n ω) :
    armRewardSum a n ω=(trajPullCount a n ω : ℝ)*trajEmpiricalMean a n ω := by
  have hN0 : (trajPullCount a n ω : ℝ)≠0 := by exact_mod_cast hN.ne'
  simp only [trajEmpiricalMean,armRewardSum]
  field_simp

lemma likelihood_gap (F : ExpFamily) {K : ℕ} (a : Fin K) (n : ℕ)
    (ω : ℕ → Fin K × ℝ) (hN : 0<trajPullCount a n ω)
    (x : ℝ) (hx : x ∈ F.Θ) :
    logLik F a n ω (F.θof (trajEmpiricalMean a n ω))-logLik F a n ω x =
      (trajPullCount a n ω : ℝ)*F.d (trajEmpiricalMean a n ω) (deriv F.b x) := by
  have hparam : F.θof (deriv F.b x)=x := F.toAllocationFamily.parameter_mean hx
  rw [ExpFamily.d,hparam]
  unfold logLik
  rw [rewardSum_eq_count_mean a n ω hN]
  ring

lemma glrNum_lower (F : ExpFamily) {K : ℕ} (a b : Fin K) (n : ℕ)
    (ω : ℕ → Fin K × ℝ)
    (hu : trajEmpiricalMean a n ω ∈ F.M) (hv : trajEmpiricalMean b n ω ∈ F.M)
    (hvu : trajEmpiricalMean b n ω ≤ trajEmpiricalMean a n ω) :
    ((logLik F a n ω (F.θof (trajEmpiricalMean a n ω))+
      logLik F b n ω (F.θof (trajEmpiricalMean b n ω)) : ℝ) : EReal) ≤ glrNum F a b n ω := by
  unfold glrNum
  apply le_iSup_of_le (F.θof (trajEmpiricalMean a n ω))
  apply le_iSup_of_le (F.θof (trajEmpiricalMean b n ω))
  exact le_iSup_of_le ⟨F.toAllocationFamily.parameter_mem hu,
    F.toAllocationFamily.parameter_mem hv,F.toAllocationFamily.parameter_strictMono.monotoneOn hv hu hvu⟩ le_rfl

lemma glrDen_upper (F : ExpFamily) {K : ℕ} (a b : Fin K) (n : ℕ)
    (ω : ℕ → Fin K × ℝ) (hNa : 0<trajPullCount a n ω) (hNb : 0<trajPullCount b n ω)
    (hu : trajEmpiricalMean a n ω ∈ F.M) (hv : trajEmpiricalMean b n ω ∈ F.M)
    (hvu : trajEmpiricalMean b n ω ≤ trajEmpiricalMean a n ω) :
    glrDen F a b n ω ≤
      ((logLik F a n ω (F.θof (trajEmpiricalMean a n ω))+
        logLik F b n ω (F.θof (trajEmpiricalMean b n ω))-
          OptProportions.pairCost F.toAllocationFamily (trajEmpiricalMean a n ω)
            (trajEmpiricalMean b n ω) (trajPullCount a n ω) (trajPullCount b n ω) : ℝ) : EReal) := by
  unfold glrDen
  apply iSup_le
  intro x
  apply iSup_le
  intro y
  apply iSup_le
  intro hxy
  apply EReal.coe_le_coe
  have hs : deriv F.b x ∈ F.M := ⟨x,hxy.1,rfl⟩
  have ht : deriv F.b y ∈ F.M := ⟨y,hxy.2.1,rfl⟩
  have hst : deriv F.b x ≤ deriv F.b y :=
    F.toAllocationFamily.mean_strictMono.monotoneOn hxy.1 hxy.2.1 hxy.2.2
  have hb := OptProportions.weighted_pair_bound F.toAllocationFamily hu hv hvu
    (Nat.cast_nonneg (trajPullCount a n ω)) (Nat.cast_nonneg (trajPullCount b n ω)) hs ht hst
  have hga := likelihood_gap F a n ω hNa x hxy.1
  have hgb := likelihood_gap F b n ω hNb y hxy.2.1
  change OptProportions.pairCost F.toAllocationFamily _ _ _ _ ≤
    (trajPullCount a n ω : ℝ)*F.d (trajEmpiricalMean a n ω) (deriv F.b x)+
      (trajPullCount b n ω : ℝ)*F.d (trajEmpiricalMean b n ω) (deriv F.b y) at hb
  linarith

lemma glr_trigger_of_cost (F : ExpFamily) {K : ℕ} (a b : Fin K) (n : ℕ)
    (ω : ℕ → Fin K × ℝ) (hNa : 0<trajPullCount a n ω) (hNb : 0<trajPullCount b n ω)
    (hu : trajEmpiricalMean a n ω ∈ F.M) (hv : trajEmpiricalMean b n ω ∈ F.M)
    (hvu : trajEmpiricalMean b n ω ≤ trajEmpiricalMean a n ω) (β : ℝ)
    (hβ : β<OptProportions.pairCost F.toAllocationFamily (trajEmpiricalMean a n ω)
      (trajEmpiricalMean b n ω) (trajPullCount a n ω) (trajPullCount b n ω)) :
    glrDen F a b n ω+(β : EReal)<glrNum F a b n ω := by
  have hd := glrDen_upper F a b n ω hNa hNb hu hv hvu
  have hn := glrNum_lower F a b n ω hu hv hvu
  have hh := add_le_add hd (le_rfl : (β : EReal) ≤ (β : EReal))
  apply lt_of_le_of_lt hh
  apply lt_of_lt_of_le _ hn
  rw [← EReal.coe_add]
  apply EReal.coe_lt_coe_iff.mpr
  linarith

end OptimalBAI.TrackStop


open BanditAlgorithm Filter Topology
open scoped ENNReal
namespace OptimalBAI.TrackStop

lemma chernoff_le_of_trigger (F : ExpFamily) {K : ℕ} (β : ℕ → ℝ)
    (ω : ℕ → Fin K × ℝ) (n : ℕ) (hn : 1≤n)
    (htrigger : ∃ a, ∀ b, b≠a → glrDen F a b n ω+(β n : EReal)<glrNum F a b n ω) :
    chernoffTime F β ω≤(n : ℕ∞) := by
  apply sInf_le
  exact ⟨n,rfl,hn,htrigger⟩

lemma log_inv_tendsto : Tendsto (fun δ : ℝ => Real.log (1/δ)) (𝓝[>] (0 : ℝ)) atTop := by
  simp only [one_div]
  exact Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero

lemma threshold_upper (α : ℝ) (r : ℕ → ℝ) (hr_pos : ∀ t, 0<r t)
    (D : ℝ) (hD : 0<D) (hr : ∀ t : ℕ, 1≤t → r t≤D*(t : ℝ)^α)
    (δ : ℝ) (hδ : 0<δ) (n : ℕ) (hn : 1≤n) :
    rateThreshold r δ n≤Real.log D+α*Real.log (n : ℝ)+Real.log (1/δ) := by
  have hnpos : (0 : ℝ)<n := by exact_mod_cast hn
  unfold rateThreshold
  have hh := Real.log_le_log (div_pos (hr_pos n) hδ)
    (div_le_div_of_nonneg_right (hr n hn) hδ.le)
  apply hh.trans_eq
  rw [Real.log_div (mul_pos hD (Real.rpow_pos_of_pos hnpos α)).ne' hδ.ne',
    Real.log_mul hD.ne' (Real.rpow_pos_of_pos hnpos α).ne',Real.log_rpow hnpos,
    Real.log_div one_ne_zero hδ.ne',Real.log_one]
  ring

end OptimalBAI.TrackStop


open BanditAlgorithm Filter Topology
open scoped ENNReal
set_option maxHeartbeats 1500000
namespace OptimalBAI.TrackStop

lemma threshold_at_ceil (α : ℝ) (r : ℕ → ℝ) (hr_pos : ∀ t, 0<r t)
    (D : ℝ) (hD : 0<D) (hr : ∀ t : ℕ, 1≤t → r t≤D*(t : ℝ)^α)
    (c A : ℝ) (hc : 0<c) (hA : 1/c<A) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      1≤Nat.ceil (A*Real.log (1/δ)) ∧
        rateThreshold r δ (Nat.ceil (A*Real.log (1/δ)))<
          c*(Nat.ceil (A*Real.log (1/δ)) : ℝ) := by
  have hAp : 0<A := (one_div_pos.mpr hc).trans hA
  let n := fun δ : ℝ => Nat.ceil (A*Real.log (1/δ))
  have hn : Tendsto n (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_nat_ceil_atTop.comp (log_inv_tendsto.const_mul_atTop hAp)
  have hnR : Tendsto (fun δ => (n δ : ℝ)) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hratio : Tendsto (fun δ => (n δ : ℝ)/Real.log (1/δ))
      (𝓝[>] (0 : ℝ)) (𝓝 A) :=
    (tendsto_nat_ceil_mul_div_atTop hAp.le).comp log_inv_tendsto
  have hinvratio : Tendsto (fun δ => Real.log (1/δ)/(n δ : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (1/A)) := by
    simpa only [inv_div,one_div] using hratio.inv₀ hAp.ne'
  have hconst : Tendsto (fun δ => Real.log D/(n δ : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using
      tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hnR)
  have hlog : Tendsto (fun δ => Real.log (n δ : ℝ)/(n δ : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 (0 : ℝ)) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h.comp hnR
  have hupper : Tendsto (fun δ => (Real.log D+α*Real.log (n δ : ℝ)+Real.log (1/δ))/(n δ : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (1/A)) := by
    simpa only [add_div,mul_div_assoc,zero_add,mul_zero] using
      (hconst.add (hlog.const_mul α)).add hinvratio
  have hAc : 1/A<c := by
    have hh := (div_lt_iff₀ hc).mp hA
    exact (div_lt_iff₀ hAp).mpr (by nlinarith)
  filter_upwards [hn.eventually_ge_atTop 1,hupper.eventually (eventually_lt_nhds hAc),
    self_mem_nhdsWithin] with δ hn1 hu hδ
  refine ⟨hn1,?_⟩
  have hnpos : (0 : ℝ)<n δ := by exact_mod_cast hn1
  have hb := threshold_upper α r hr_pos D hD hr δ hδ (n δ) hn1
  have hh := (div_lt_iff₀ hnpos).mp hu
  exact hb.trans_lt hh

lemma threshold_sublinear_eventual (α : ℝ) (r : ℕ → ℝ) (hr_pos : ∀ t, 0<r t)
    (D : ℝ) (hD : 0<D) (hr : ∀ t : ℕ, 1≤t → r t≤D*(t : ℝ)^α)
    (δ : ℝ) (hδ : 0<δ) (c : ℝ) (hc : 0<c) :
    ∀ᶠ n : ℕ in atTop, rateThreshold r δ n<c*(n : ℝ) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)/(n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    have h : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 (0 : ℝ)) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h.comp hnat
  have hconst : Tendsto (fun n : ℕ => (Real.log D+Real.log (1/δ))/(n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using
      tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hnat)
  have hu : Tendsto (fun n : ℕ => (Real.log D+α*Real.log (n : ℝ)+Real.log (1/δ))/(n : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [add_div,mul_div_assoc,add_comm,add_left_comm,add_assoc,add_zero,mul_zero] using
      hconst.add (hlog.const_mul α)
  filter_upwards [hu.eventually (eventually_lt_nhds hc),eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : (0 : ℝ)<n := by exact_mod_cast hn1
  exact (threshold_upper α r hr_pos D hD hr δ hδ n hn1).trans_lt ((div_lt_iff₀ hnpos).mp hn)

end OptimalBAI.TrackStop


open BanditAlgorithm Filter Topology
set_option maxHeartbeats 1500000
namespace OptimalBAI.TrackStop

lemma threshold_above_ceil (α : ℝ) (r : ℕ → ℝ) (hr_pos : ∀ t, 0<r t)
    (D : ℝ) (hD : 0<D) (hr : ∀ t : ℕ, 1≤t → r t≤D*(t : ℝ)^α)
    (c A : ℝ) (hc : 0<c) (hA : 1/c<A) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      1≤Nat.ceil (A*Real.log (1/δ)) ∧ ∀ n : ℕ, Nat.ceil (A*Real.log (1/δ))≤n →
        rateThreshold r δ n<c*(n : ℝ) := by
  have hAp : 0<A := (one_div_pos.mpr hc).trans hA
  have hAc : 1/A<c := by
    have hh := (div_lt_iff₀ hc).mp hA
    exact (div_lt_iff₀ hAp).mpr (by nlinarith)
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)/(n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    have h : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 (0 : ℝ)) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h.comp hnat
  have hconst : Tendsto (fun n : ℕ => Real.log D/(n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using
      tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hnat)
  have hu : Tendsto (fun n : ℕ => (Real.log D+α*Real.log (n : ℝ))/(n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [add_div,mul_div_assoc,add_zero,mul_zero] using hconst.add (hlog.const_mul α)
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hu.eventually (eventually_lt_nhds (sub_pos.mpr hAc)))
  have hn : Tendsto (fun δ : ℝ => Nat.ceil (A*Real.log (1/δ))) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_nat_ceil_atTop.comp (log_inv_tendsto.const_mul_atTop hAp)
  filter_upwards [hn.eventually_ge_atTop T,hn.eventually_ge_atTop 1,
    log_inv_tendsto.eventually_gt_atTop 0,self_mem_nhdsWithin] with δ hnT hn1 hlogδ hδ
  refine ⟨hn1,?_⟩
  intro n hnn
  have hn1' := hn1.trans hnn
  have hnp : (0 : ℝ)<n := by exact_mod_cast hn1'
  have hceil : A*Real.log (1/δ)≤(n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hnn)
  have hratio : Real.log (1/δ)/(n : ℝ)≤1/A := by
    apply (div_le_iff₀ hnp).mpr
    have hh : Real.log (1/δ)≤(n : ℝ)/A := (le_div_iff₀ hAp).mpr (by nlinarith)
    calc
      _≤(n : ℝ)/A := hh
      _=1/A*(n : ℝ) := by ring
  have hh := hT n (hnT.trans hnn)
  have hh' : (Real.log D+α*Real.log (n : ℝ)+Real.log (1/δ))/(n : ℝ)<c := by
    rw [add_div]
    linarith
  exact (threshold_upper α r hr_pos D hD hr δ hδ n hn1').trans_lt ((div_lt_iff₀ hnp).mp hh')

end OptimalBAI.TrackStop


open Filter Topology
namespace OptimalBAI.TrackStop

lemma summable_exp_sqrt (c : ℝ) (hc : 0 < c) :
    Summable (fun n : ℕ => Real.exp (-c*Real.sqrt n)) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)^2*Real.exp (-c*Real.sqrt n)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 4 c hc).comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    convert h using 1
    funext n
    simp only [Function.comp_apply]
    rw [show (4 : ℝ)=(4 : ℕ) by norm_num,Real.rpow_natCast]
    have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    rw [show (Real.sqrt (n : ℝ))^4=((Real.sqrt (n : ℝ))^2)^2 by ring,hs]
  have hb : ∀ᶠ n : ℕ in atTop, (n : ℝ)^2*Real.exp (-c*Real.sqrt n) ≤ 1 :=
    (ht.eventually (eventually_le_nhds (show (0 : ℝ)<1 by norm_num)))
  apply Summable.of_norm_bounded_eventually_nat
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  filter_upwards [hb,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : (0 : ℝ)<n := by exact_mod_cast hn1
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact (le_div_iff₀ (sq_pos_of_pos hnpos)).2 (by nlinarith)

lemma summable_exp_sqrt_shift (c C : ℝ) (hc : 0<c) :
    Summable (fun n : ℕ => Real.exp (-c*(Real.sqrt n-C))) := by
  have h := (summable_exp_sqrt c hc).mul_left (Real.exp (c*C))
  apply h.congr
  intro n
  rw [← Real.exp_add]
  congr 1
  ring

end OptimalBAI.TrackStop


open Filter Topology
namespace OptimalBAI.TrackStop

lemma summable_weighted_exp_sqrt (c : ℝ) (hc : 0<c) :
    Summable (fun n : ℕ => (n+1 : ℝ)*Real.exp (-c*Real.sqrt n)) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)^3*Real.exp (-c*Real.sqrt n)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 6 c hc).comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    convert h using 1
    funext n
    simp only [Function.comp_apply]
    rw [show (6 : ℝ)=(6 : ℕ) by norm_num,Real.rpow_natCast]
    have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ)≤n)
    rw [show (Real.sqrt (n : ℝ))^6=((Real.sqrt (n : ℝ))^2)^3 by ring,hs]
  have hb : ∀ᶠ n : ℕ in atTop, (n : ℝ)^3*Real.exp (-c*Real.sqrt n)≤1/2 :=
    ht.eventually (eventually_le_nhds (by norm_num : (0 : ℝ)<1/2))
  apply Summable.of_norm_bounded_eventually_nat
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1<(2 : ℕ)))
  filter_upwards [hb,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hp : (0 : ℝ)<n := by exact_mod_cast hn1
  rw [Real.norm_eq_abs,abs_of_pos (mul_pos (by positivity) (Real.exp_pos _))]
  apply (le_div_iff₀ (sq_pos_of_pos hp)).mpr
  have he := Real.exp_pos (-c*Real.sqrt n)
  have hnp : (1 : ℝ)≤n := by exact_mod_cast hn1
  nlinarith [mul_nonneg (show 0≤(n : ℝ)^2 by positivity) (show 0≤(n : ℝ)-1 by linarith)]

lemma summable_weighted_exp_sqrt_shift (c C : ℝ) (hc : 0<c) :
    Summable (fun n : ℕ => (n+1 : ℝ)*Real.exp (-c*(Real.sqrt n-C))) := by
  have h := (summable_weighted_exp_sqrt c hc).mul_left (Real.exp (c*C))
  apply h.congr
  intro n
  rw [←mul_assoc,mul_comm (Real.exp (c*C)) (n+1 : ℝ),mul_assoc,←Real.exp_add]
  congr 1
  ring

end OptimalBAI.TrackStop


open MeasureTheory ProbabilityTheory BanditAlgorithm Preorder
namespace OptimalBAI.TrackStop

def histPulls {K n : ℕ} (a : Fin K) (h : BanditHistory K n) : ℕ :=
  ∑ i, if (h i).1=a then 1 else 0

noncomputable def histSum {K n : ℕ} (a : Fin K) (h : BanditHistory K n) : ℝ :=
  ∑ i, if (h i).1=a then (h i).2 else 0

lemma histPulls_measurable {K n : ℕ} (a : Fin K) : Measurable (histPulls (n := n) a) := by
  unfold histPulls
  apply Finset.measurable_sum
  intro i hi
  have hm : Measurable (fun h : BanditHistory K n => (h i).1) := by fun_prop
  exact measurable_const.ite (measurableSet_eq_fun hm measurable_const) measurable_const

lemma histSum_measurable {K n : ℕ} (a : Fin K) : Measurable (histSum (n := n) a) := by
  unfold histSum
  apply Finset.measurable_sum
  intro i hi
  have hm : Measurable (fun h : BanditHistory K n => (h i).1) := by fun_prop
  have hr : Measurable (fun h : BanditHistory K n => (h i).2) := by fun_prop
  exact hr.ite (measurableSet_eq_fun hm measurable_const) measurable_const

lemma histPulls_snoc {K n : ℕ} (a : Fin K) (h : BanditHistory K n) (z : Fin K × ℝ) :
    histPulls a (Fin.snoc h z)=histPulls a h + if z.1=a then 1 else 0 := by
  classical
  unfold histPulls
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]

lemma histSum_snoc {K n : ℕ} (a : Fin K) (h : BanditHistory K n) (z : Fin K × ℝ) :
    histSum a (Fin.snoc h z)=histSum a h + if z.1=a then z.2 else 0 := by
  classical
  unfold histSum
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]

lemma histPulls_prefix {K : ℕ} (a : Fin K) (t : ℕ) (ω : ℕ → Fin K × ℝ) :
    histPulls a (banditTrajPrefix K t ω)=trajPullCount a t ω := by
  classical
  unfold histPulls trajPullCount banditTrajPrefix
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if (ω i).1=a then (1 : ℕ) else 0) t

lemma histPulls_native {K n : ℕ} (a : Fin K) (h : BanditHistory K n) :
    histPulls a h=armPullCount a h := by
  classical
  unfold histPulls armPullCount
  rw [Set.toFinset_ofPred, Finset.card_filter]

lemma histSum_prefix {K : ℕ} (a : Fin K) (t : ℕ) (ω : ℕ → Fin K × ℝ) :
    histSum a (banditTrajPrefix K t ω)=
      ∑ i ∈ (Finset.range t).filter (fun i => (ω i).1=a), (ω i).2 := by
  classical
  unfold histSum banditTrajPrefix
  rw [Finset.sum_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if (ω i).1=a then (ω i).2 else 0) t

lemma initial_prefix_law {X : Type*} [MeasurableSpace X]
    (μ₀ : Measure X) [IsProbabilityMeasure μ₀]
    (κ : (t : ℕ) → Kernel (Finset.Iic t → X) X) [∀ t, IsMarkovKernel (κ t)] :
    (Kernel.trajMeasure (X := fun _ : ℕ => X) μ₀ κ).map (frestrictLe 0) =
      μ₀.map (MeasurableEquiv.piUnique (fun _i : Finset.Iic 0 => X)).symm := by
  rw [Kernel.trajMeasure,Measure.map_comp _ _ (measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe,Kernel.partialTraj_self,Measure.id_comp]

lemma iicHistory_snoc {K : ℕ} (t : ℕ) (ω : ℕ → Fin K × ℝ) :
    banditIicHistory K (t+1) (frestrictLe (t+1) ω) =
      Fin.snoc (banditIicHistory K t (frestrictLe t ω)) (ω (t+1)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]; rfl
  · rw [Fin.snoc_castSucc]; rfl

lemma iicHistory_prefix {K : ℕ} (t : ℕ) (ω : ℕ → Fin K × ℝ) :
    banditIicHistory K t (frestrictLe t ω)=banditTrajPrefix K (t+1) ω := rfl

end OptimalBAI.TrackStop


open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal
namespace OptimalBAI.TrackStop

lemma trajectory_lintegral_constant {X : Type*} [MeasurableSpace X]
    (μ₀ : Measure X) [IsProbabilityMeasure μ₀]
    (κ : (t : ℕ) → Kernel (Finset.Iic t → X) X) [∀ t, IsMarkovKernel (κ t)]
    (f : (t : ℕ) → (Finset.Iic t → X) → ℝ≥0∞)
    (g : (t : ℕ) → (Finset.Iic t → X) → X → ℝ≥0∞)
    (hf : ∀ t, Measurable (f t)) (hg : ∀ t, Measurable (g t).uncurry)
    (heq : ∀ t (ω : ℕ → X), f (t+1) (frestrictLe (t+1) ω) = g t (frestrictLe t ω) (ω (t+1)))
    (hmean : ∀ t h, (∫⁻ z, g t h z ∂κ t h) = f t h)
    (hinit : (∫⁻ h, f 0 h ∂μ₀.map (MeasurableEquiv.piUnique (fun _i : Finset.Iic 0 => X)).symm)=1) :
    ∀ t, (∫⁻ ω, f t (frestrictLe t ω) ∂Kernel.trajMeasure (X := fun _ : ℕ => X) μ₀ κ)=1 := by
  let P := Kernel.trajMeasure (X := fun _ : ℕ => X) μ₀ κ
  intro t
  induction t with
  | zero =>
    rw [← lintegral_map (hf 0) (measurable_frestrictLe 0),
      initial_prefix_law]
    exact hinit
  | succ t ih =>
    let Q := P.map (frestrictLe t)
    have hjoint : Q ⊗ₘ κ t = P.map (fun ω => (frestrictLe t ω,ω (t+1))) :=
      Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    calc
      _ = ∫⁻ p, (g t).uncurry p ∂P.map (fun ω => (frestrictLe t ω,ω (t+1))) := by
        rw [lintegral_map (hg t) (by fun_prop)]
        exact lintegral_congr (heq t)
      _ = ∫⁻ p, (g t).uncurry p ∂(Q ⊗ₘ κ t) := by rw [hjoint]
      _ = ∫⁻ h, ∫⁻ z, g t h z ∂κ t h ∂Q := Measure.lintegral_compProd (hg t)
      _ = ∫⁻ h, f t h ∂Q := by simp_rw [hmean]
      _ = _ := by rw [lintegral_map (hf t) (measurable_frestrictLe t)]; exact ih

end OptimalBAI.TrackStop


open MeasureTheory
namespace OptimalBAI.TrackStop.ExpFamily

lemma normalized_tilt (F : ExpFamily) (θ ℓ : ℝ) (hθ : θ+ℓ ∈ F.Θ) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (ℓ*x-(F.b (θ+ℓ)-F.b θ))) ∂F.arm θ)=1 := by
  rw [arm,lintegral_withDensity_eq_lintegral_mul F.ξ (by fun_prop) (by fun_prop)]
  calc
    _ = ∫⁻ x, ENNReal.ofReal (Real.exp ((θ+ℓ)*x-F.b (θ+ℓ))) ∂F.ξ := by
      apply lintegral_congr
      intro x
      simp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
      congr 1
      ring
    _ = 1 := F.isNormalized _ hθ

end OptimalBAI.TrackStop.ExpFamily


open MeasureTheory ProbabilityTheory BanditAlgorithm Preorder
open scoped ENNReal
set_option maxHeartbeats 2000000
namespace OptimalBAI.TrackStop

noncomputable def histExp (F : ExpFamily) {K n : ℕ} (a : Fin K) (θ ℓ : ℝ)
    (h : BanditHistory K n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (ℓ * histSum a h -
    (F.b (θ+ℓ)-F.b θ) * (histPulls a h : ℝ)))

lemma histExp_measurable (F : ExpFamily) {K n : ℕ} (a : Fin K) (θ ℓ : ℝ) :
    Measurable (histExp F (n := n) a θ ℓ) := by
  unfold histExp
  exact ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp ((measurable_const.mul (histSum_measurable a)).sub
      (measurable_const.mul ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
        (histPulls_measurable a)))))

lemma histExp_snoc (F : ExpFamily) {K n : ℕ} (a : Fin K) (θ ℓ : ℝ)
    (h : BanditHistory K n) (z : Fin K × ℝ) :
    histExp F a θ ℓ (Fin.snoc h z) = histExp F a θ ℓ h *
      (if z.1=a then ENNReal.ofReal (Real.exp (ℓ*z.2-(F.b (θ+ℓ)-F.b θ))) else 1) := by
  classical
  unfold histExp
  rw [histSum_snoc,histPulls_snoc]
  by_cases hz : z.1=a
  · simp only [hz,ite_true,Nat.cast_add,Nat.cast_one]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
    congr 2
    ring
  · simp [hz]

lemma histExp_step_mean (F : ExpFamily) {K n : ℕ} (θ : Fin K → F.Θ)
    (π : BanditPolicy K) (a : Fin K) (ℓ : ℝ) (hℓ : (θ a : ℝ)+ℓ ∈ F.Θ)
    (h : BanditHistory K n) :
    (∫⁻ z, histExp F a (θ a) ℓ (Fin.snoc h z)
      ∂banditStepKernel (expFamilyBandit F θ) π n h) = histExp F a (θ a) ℓ h := by
  classical
  have hm : Measurable (fun z : Fin K × ℝ => histExp F a (θ a) ℓ (Fin.snoc h z)) :=
    (histExp_measurable F a (θ a) ℓ).comp
      (measurable_banditHistorySnoc.comp measurable_prodMk_left)
  rw [banditStepKernel,Kernel.lintegral_compProd _ _ _
    hm]
  simp only [Kernel.comap_apply]
  change (∫⁻ i, ∫⁻ r, histExp F a (θ a) ℓ (Fin.snoc h (i,r)) ∂F.arm (θ i)
    ∂π.select n h) = _
  have hinner (i : Fin K) :
      (∫⁻ r, histExp F a (θ a) ℓ (Fin.snoc h (i,r))
        ∂F.arm (θ i)) =
        histExp F a (θ a) ℓ h := by
    change (∫⁻ r, histExp F a (θ a) ℓ (Fin.snoc h (i,r)) ∂F.arm (θ i)) = _
    simp_rw [histExp_snoc]
    by_cases hi : i=a
    · subst i
      simp only [ite_true]
      rw [lintegral_const_mul _ (by fun_prop), F.normalized_tilt _ _ hℓ,mul_one]
    · simp only [hi,ite_false,mul_one]
      letI := F.isProbabilityMeasure_arm (θ i).2
      simp
  simp_rw [hinner]
  simp

lemma histExp_trajectory_mean (F : ExpFamily) {K : ℕ} (θ : Fin K → F.Θ)
    (π : BanditPolicy K) (a : Fin K) (ℓ : ℝ) (hℓ : (θ a : ℝ)+ℓ ∈ F.Θ) (n : ℕ) :
    (∫⁻ ω, histExp F a (θ a) ℓ (banditTrajPrefix K n ω)
      ∂banditTrajMeasure (expFamilyBandit F θ) π)=1 := by
  let ν := expFamilyBandit F θ
  let μ₀ := banditStepKernel ν π 0 (fun i => i.elim0)
  let κ := banditTrajKernel ν π
  let f := fun t h => histExp F a (θ a) ℓ (banditIicHistory K t h)
  let g := fun t h z => histExp F a (θ a) ℓ (Fin.snoc (banditIicHistory K t h) z)
  have hf t : Measurable (f t) :=
    (histExp_measurable F a (θ a) ℓ).comp measurable_banditIicHistory
  have hg t : Measurable (g t).uncurry :=
    (histExp_measurable F a (θ a) ℓ).comp
      (measurable_banditHistorySnoc.comp
        ((measurable_banditIicHistory.comp measurable_fst).prodMk measurable_snd))
  have heq (t : ℕ) (ω : ℕ → Fin K × ℝ) : f (t+1) (frestrictLe (t+1) ω) = g t (frestrictLe t ω) (ω (t+1)) := by
    dsimp [f,g]
    rw [iicHistory_snoc]
  have hmean t h : (∫⁻ z, g t h z ∂κ t h)=f t h := by
    exact histExp_step_mean F θ π a ℓ hℓ _
  have hinit : (∫⁻ h, f 0 h ∂μ₀.map
      (MeasurableEquiv.piUnique (fun _i : Finset.Iic 0 => Fin K × ℝ)).symm)=1 := by
    rw [lintegral_map (hf 0) (MeasurableEquiv.piUnique _).symm.measurable]
    have heq0 z : f 0 ((MeasurableEquiv.piUnique _).symm z) =
        histExp F a (θ a) ℓ (Fin.snoc (fun i : Fin 0 => i.elim0) z) := by
      apply congrArg (histExp F a (θ a) ℓ)
      funext i
      have hi : i=0 := Fin.eq_zero i
      subst i
      rfl
    simp_rw [heq0]
    rw [histExp_step_mean F θ π a ℓ hℓ]
    simp [histExp,histSum,histPulls]
  cases n with
  | zero => simp [histExp,histSum,histPulls,banditTrajPrefix]
  | succ t =>
    exact trajectory_lintegral_constant μ₀ κ f g hf hg heq hmean hinit t

end OptimalBAI.TrackStop


open MeasureTheory Filter Topology
namespace OptimalBAI.TrackStop

lemma small_tilts (F : ExpFamily) (θ : ℝ) (hθ : θ ∈ F.Θ) (ε : ℝ) (hε : 0 < ε) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ θ+ℓ ∈ F.Θ ∧ θ-ℓ ∈ F.Θ ∧
      F.b (θ+ℓ)-F.b θ-ℓ*deriv F.b θ ≤ ℓ*ε/2 ∧
      F.b (θ-ℓ)-F.b θ+ℓ*deriv F.b θ ≤ ℓ*ε/2 := by
  have hd : HasDerivAt F.b (deriv F.b θ) θ :=
    (F.toAllocationFamily.b_differentiableAt hθ).hasDerivAt
  have hb := hd.isLittleO.bound (show 0 < ε/2 by positivity)
  have he : ∀ᶠ x in 𝓝 θ, x ∈ F.Θ ∧
      |F.b x-F.b θ-(x-θ)*deriv F.b θ| ≤ ε/2*|x-θ| := by
    filter_upwards [F.isOpen_Θ.mem_nhds hθ,hb] with x hx hbx
    exact ⟨hx,by simpa [Real.norm_eq_abs,smul_eq_mul] using hbx⟩
  obtain ⟨r,hr,hrb⟩ := Metric.eventually_nhds_iff.mp he
  let ℓ := r/2
  have hℓ : 0 < ℓ := by dsimp [ℓ]; positivity
  have hp := hrb (show dist (θ+ℓ) θ < r by
    rw [Real.dist_eq,add_sub_cancel_left,abs_of_pos hℓ]; dsimp [ℓ]; linarith)
  have hm := hrb (show dist (θ-ℓ) θ < r by
    rw [Real.dist_eq,sub_sub_cancel_left,abs_neg,abs_of_pos hℓ]; dsimp [ℓ]; linarith)
  refine ⟨ℓ,hℓ,hp.1,hm.1,?_,?_⟩
  · have hh := (abs_le.mp hp.2).2
    simp only [add_sub_cancel_left,abs_of_pos hℓ] at hh
    nlinarith
  · have hh := (abs_le.mp hm.2).2
    simp only [sub_sub_cancel_left,abs_neg,abs_of_pos hℓ,neg_mul,sub_neg_eq_add] at hh
    nlinarith

end OptimalBAI.TrackStop


open MeasureTheory ProbabilityTheory BanditAlgorithm Filter Topology
open scoped ENNReal
set_option maxHeartbeats 1500000
namespace OptimalBAI.TrackStop

noncomputable def histAverage {K n : ℕ} (a : Fin K) (h : BanditHistory K n) : ℝ :=
  histSum a h / (histPulls a h : ℝ)

lemma histAverage_prefix {K : ℕ} (a : Fin K) (t : ℕ) (ω : ℕ → Fin K × ℝ) :
    histAverage a (banditTrajPrefix K t ω)=trajEmpiricalMean a t ω := by
  rw [histAverage,histPulls_prefix,histSum_prefix]
  rfl

lemma exp_process_markov (F : ExpFamily) {K : ℕ} (θ : Fin K → F.Θ)
    (π : BanditPolicy K) (a : Fin K) (ℓ : ℝ) (hℓ : (θ a : ℝ)+ℓ ∈ F.Θ)
    (n : ℕ) (x : ℝ) :
    banditTrajMeasure (expFamilyBandit F θ) π
      {ω | ENNReal.ofReal (Real.exp x) ≤ histExp F a (θ a) ℓ (banditTrajPrefix K n ω)}
      ≤ ENNReal.ofReal (Real.exp (-x)) := by
  have h := meas_ge_le_lintegral_div
    (μ := banditTrajMeasure (expFamilyBandit F θ) π)
    (f := fun ω => histExp F a (θ a) ℓ (banditTrajPrefix K n ω))
    ((histExp_measurable F a (θ a) ℓ).comp measurable_banditTrajPrefix).aemeasurable
    (show ENNReal.ofReal (Real.exp x) ≠ 0 by simp [Real.exp_pos]) ENNReal.ofReal_ne_top
  rw [histExp_trajectory_mean F θ π a ℓ hℓ n,one_div,
    ← ENNReal.ofReal_inv_of_pos (Real.exp_pos x),← Real.exp_neg] at h
  exact h

lemma empirical_tail_bound (F : ExpFamily) {K : ℕ} (θ : Fin K → F.Θ)
    (π : BanditPolicy K) (a : Fin K) (ε : ℝ) (hε : 0<ε) :
    ∃ c : ℝ, 0<c ∧ ∀ (n : ℕ) (g : ℝ),
      banditTrajMeasure (expFamilyBandit F θ) π
        {ω | 0<trajPullCount a n ω ∧ g≤(trajPullCount a n ω : ℝ) ∧
          ε≤|trajEmpiricalMean a n ω-meanVec F θ a|} ≤
        2*ENNReal.ofReal (Real.exp (-c*g)) := by
  classical
  obtain ⟨ℓ,hℓ,hp,hm,hup,hlo⟩ := small_tilts F (θ a) (θ a).2 ε hε
  let c := ℓ*ε/2
  have hc : 0<c := by dsimp [c]; positivity
  refine ⟨c,hc,?_⟩
  intro n g
  let P := banditTrajMeasure (expFamilyBandit F θ) π
  let E (l : ℝ) := {ω | ENNReal.ofReal (Real.exp (c*g)) ≤
    histExp F a (θ a) l (banditTrajPrefix K n ω)}
  have hsubset : {ω | 0<trajPullCount a n ω ∧ g≤(trajPullCount a n ω : ℝ) ∧
      ε≤|trajEmpiricalMean a n ω-meanVec F θ a|} ⊆ E ℓ ∪ E (-ℓ) := by
    intro ω hω
    let h := banditTrajPrefix K n ω
    let N : ℝ := histPulls a h
    let S : ℝ := histSum a h
    let μ : ℝ := deriv F.b (θ a)
    have hN : 0<N := by dsimp [N,h]; rw [histPulls_prefix]; exact_mod_cast hω.1
    have hg : g≤N := by simpa [N,h,histPulls_prefix] using hω.2.1
    have hav : ε≤|S/N-μ| := by
      simpa only [← histAverage_prefix a n ω,histAverage,meanVec] using hω.2.2
    rcases (le_abs.mp hav) with hu | hl
    · apply Or.inl
      have hS : (μ+ε)*N ≤ S := (le_div_iff₀ hN).mp (by linarith : μ+ε≤S/N)
      have hb := mul_le_mul_of_nonneg_right hup hN.le
      have hS' := mul_le_mul_of_nonneg_left hS hℓ.le
      have hcg := mul_le_mul_of_nonneg_left hg hc.le
      have hex : c*g ≤ ℓ*S-(F.b ((θ a : ℝ)+ℓ)-F.b (θ a))*N := by
        dsimp [c,μ] at *
        nlinarith
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hex)
    · apply Or.inr
      have hS : S ≤ (μ-ε)*N := (div_le_iff₀ hN).mp (by linarith : S/N≤μ-ε)
      have hb := mul_le_mul_of_nonneg_right hlo hN.le
      have hS' := mul_le_mul_of_nonneg_left hS hℓ.le
      have hcg := mul_le_mul_of_nonneg_left hg hc.le
      have hex : c*g ≤ (-ℓ)*S-(F.b ((θ a : ℝ)+(-ℓ))-F.b (θ a))*N := by
        rw [← sub_eq_add_neg]
        dsimp [c,μ] at *
        nlinarith
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hex)
  calc
    _ ≤ P (E ℓ ∪ E (-ℓ)) := measure_mono hsubset
    _ ≤ P (E ℓ)+P (E (-ℓ)) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-c*g))+ENNReal.ofReal (Real.exp (-c*g)) := by
      apply add_le_add
      · simpa only [neg_mul] using exp_process_markov F θ π a ℓ hp n (c*g)
      · simpa only [neg_mul] using
          exp_process_markov F θ π a (-ℓ) (by simpa only [sub_eq_add_neg] using hm) n (c*g)
    _ = _ := by rw [two_mul]

end OptimalBAI.TrackStop


open MeasureTheory BanditAlgorithm Filter Topology
open scoped ENNReal
set_option maxHeartbeats 1500000
namespace OptimalBAI.TrackStop

lemma trajPullCount_measurable {K : ℕ} (a : Fin K) (n : ℕ) :
    Measurable (trajPullCount a n) := by
  simpa only [Function.comp_def,histPulls_prefix] using
    (histPulls_measurable (n := n) a).comp measurable_banditTrajPrefix

lemma trajEmpiricalMean_measurable {K : ℕ} (a : Fin K) (n : ℕ) :
    Measurable (trajEmpiricalMean a n) := by
  have hN : Measurable (fun h : BanditHistory K n => (histPulls a h : ℝ)) :=
    (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp (histPulls_measurable a)
  have hav : Measurable (histAverage (n := n) a) := (histSum_measurable a).div hN
  simpa only [Function.comp_def,histAverage_prefix] using hav.comp measurable_banditTrajPrefix

noncomputable def badEstimate (F : ExpFamily) {K : ℕ} (θ : Fin K → F.Θ)
    (C ε : ℝ) (n : ℕ) (a : Fin K) : Set (ℕ → Fin K × ℝ) :=
  {ω | 0<trajPullCount a n ω ∧ Real.sqrt n-C≤(trajPullCount a n ω : ℝ) ∧
    ε≤|trajEmpiricalMean a n ω-meanVec F θ a|}

lemma badEstimate_measurable (F : ExpFamily) {K : ℕ} (θ : Fin K → F.Θ)
    (C ε : ℝ) (n : ℕ) (a : Fin K) : MeasurableSet (badEstimate F θ C ε n a) := by
  have hN := trajPullCount_measurable a n
  have hNr : Measurable (fun ω : ℕ → Fin K × ℝ => (trajPullCount a n ω : ℝ)) :=
    (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp hN
  exact (measurableSet_lt measurable_const hN).inter
    ((measurableSet_le measurable_const hNr).inter
      (measurableSet_le measurable_const ((trajEmpiricalMean_measurable a n).sub measurable_const).abs))

noncomputable def badDelay (F : ExpFamily) {K : ℕ} (θ : Fin K → F.Θ)
    (C ε : ℝ) (ω : ℕ → Fin K × ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, ∑ a : Fin K, (badEstimate F θ C ε n a).indicator (fun _ => (n+1 : ℝ≥0∞)) ω

lemma badDelay_measurable (F : ExpFamily) {K : ℕ} (θ : Fin K → F.Θ) (C ε : ℝ) :
    Measurable (badDelay F θ C ε) := by
  apply Measurable.ennreal_tsum
  intro n
  apply Finset.measurable_sum
  intro a ha
  exact measurable_const.indicator (badEstimate_measurable F θ C ε n a)

lemma badDelay_integral_finite (F : ExpFamily) {K : ℕ} (θ : Fin K → F.Θ)
    (π : BanditPolicy K) (C ε : ℝ) (hε : 0<ε) :
    (∫⁻ ω, badDelay F θ C ε ω ∂banditTrajMeasure (expFamilyBandit F θ) π)≠⊤ := by
  classical
  let P := banditTrajMeasure (expFamilyBandit F θ) π
  have hsingle (a : Fin K) : (∑' n : ℕ, (n+1 : ℝ≥0∞)*P (badEstimate F θ C ε n a))≠⊤ := by
    obtain ⟨c,hc,htail⟩ := empirical_tail_bound F θ π a ε hε
    apply ne_top_of_le_ne_top
      (((summable_weighted_exp_sqrt_shift c C hc).mul_left 2).tsum_ofReal_ne_top)
    apply ENNReal.tsum_le_tsum
    intro n
    calc
      _≤(n+1 : ℝ≥0∞)*(2*ENNReal.ofReal (Real.exp (-c*(Real.sqrt n-C)))) := by
        gcongr
        exact htail n _
      _=ENNReal.ofReal (2*((n+1 : ℝ)*Real.exp (-c*(Real.sqrt n-C)))) := by
        rw [ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_mul (by positivity)]
        rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,ENNReal.ofReal_natCast,ENNReal.ofReal_one]
        norm_num
        ring
  have heq : (∫⁻ ω, badDelay F θ C ε ω ∂P)=
      ∑ a : Fin K, ∑' n : ℕ, (n+1 : ℝ≥0∞)*P (badEstimate F θ C ε n a) := by
    unfold badDelay
    rw [lintegral_tsum (fun n => (Finset.measurable_sum _ (fun a _ =>
      measurable_const.indicator (badEstimate_measurable F θ C ε n a))).aemeasurable)]
    simp_rw [lintegral_finset_sum _ (fun a _ =>
      measurable_const.indicator (badEstimate_measurable F θ C ε _ a)),
      lintegral_indicator_const (badEstimate_measurable F θ C ε _ _) ]
    exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
  rw [heq]
  exact ENNReal.sum_ne_top.mpr (fun a _ => hsingle a)

lemma badDelay_dominates (F : ExpFamily) {K : ℕ} (θ : Fin K → F.Θ)
    (C ε : ℝ) (ω : ℕ → Fin K × ℝ) (n : ℕ) (a : Fin K)
    (he : ω∈badEstimate F θ C ε n a) : (n+1 : ℝ≥0∞)≤badDelay F θ C ε ω := by
  classical
  have hterm : (n+1 : ℝ≥0∞)≤∑ b : Fin K, (badEstimate F θ C ε n b).indicator (fun _ => (n+1 : ℝ≥0∞)) ω := by
    simpa only [Set.indicator_of_mem he] using
      (Finset.single_le_sum (fun b _ => bot_le : ∀ b∈(Finset.univ : Finset (Fin K)),
        (0 : ℝ≥0∞)≤(badEstimate F θ C ε n b).indicator (fun _ => (n+1 : ℝ≥0∞)) ω) (Finset.mem_univ a))
  exact hterm.trans (ENNReal.le_tsum n)

end OptimalBAI.TrackStop


open MeasureTheory ProbabilityTheory BanditAlgorithm Filter Topology
open scoped ENNReal
set_option maxHeartbeats 1500000
namespace OptimalBAI.TrackStop

lemma empirical_deviations_eventually (F : ExpFamily) {K : ℕ} (θ : Fin K → F.Θ)
    (π : BanditPolicy K) (a : Fin K) (C : ℝ) (ε : ℝ) (hε : 0<ε) :
    ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F θ) π, ∀ᶠ n : ℕ in atTop,
      ¬(0<trajPullCount a n ω ∧ Real.sqrt n-C≤(trajPullCount a n ω : ℝ) ∧
        ε≤|trajEmpiricalMean a n ω-meanVec F θ a|) := by
  obtain ⟨c,hc,htail⟩ := empirical_tail_bound F θ π a ε hε
  apply ae_eventually_notMem
  apply ne_top_of_le_ne_top
    (((summable_exp_sqrt_shift c C hc).mul_left 2).tsum_ofReal_ne_top)
  apply ENNReal.tsum_le_tsum
  intro n
  calc
    _ ≤ 2*ENNReal.ofReal (Real.exp (-c*(Real.sqrt n-C))) := htail n _
    _ = ENNReal.ofReal (2*Real.exp (-c*(Real.sqrt n-C))) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num

lemma empirical_consistency_forced (F : ExpFamily) {K : ℕ} (θ : Fin K → F.Θ)
    (π : BanditPolicy K) (C : ℝ)
    (hforced : ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F θ) π,
      ∀ᶠ n : ℕ in atTop, ∀ a, Real.sqrt n-C≤(trajPullCount a n ω : ℝ)) :
    ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F θ) π,
      Tendsto (fun n => trajMeanVec n ω) atTop (𝓝 (meanVec F θ)) := by
  have heach : ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F θ) π, ∀ a (m : ℕ),
      ∀ᶠ n : ℕ in atTop,
        ¬(0<trajPullCount a n ω ∧ Real.sqrt n-C≤(trajPullCount a n ω : ℝ) ∧
          1/(m+1 : ℝ)≤|trajEmpiricalMean a n ω-meanVec F θ a|) := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro m
    exact empirical_deviations_eventually F θ π a C _ (by positivity)
  have hg : ∀ᶠ n : ℕ in atTop, 0<Real.sqrt n-C :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop C |>.mono
      (fun n hn => sub_pos.mpr hn)
  filter_upwards [heach,hforced] with ω hω hforce
  apply tendsto_pi_nhds.mpr
  intro a
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω a m,hforce,hg] with n hn hfn hgn
  have hp : 0<trajPullCount a n ω := by
    exact_mod_cast (hgn.trans_le (hfn a))
  have hh : |trajEmpiricalMean a n ω-meanVec F θ a| < 1/(m+1 : ℝ) := by
    exact lt_of_not_ge (fun h => hn ⟨hp,hfn a,h⟩)
  exact (by simpa [Real.dist_eq,trajMeanVec] using hh.trans hm)

end OptimalBAI.TrackStop


open MeasureTheory ProbabilityTheory BanditAlgorithm Preorder
open scoped ENNReal
namespace OptimalBAI.TrackStop

lemma selectAtom_measurable {K n : ℕ} (π : BanditPolicy K) :
    Measurable (fun p : BanditHistory K n × Fin K => π.select n p.1 {p.2}) := by
  apply measurable_from_prod_countable_left
  intro a
  exact Kernel.measurable_coe _ (measurableSet_singleton a)

lemma step_support {K n : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K)
    (h : BanditHistory K n) :
    ∀ᵐ z ∂banditStepKernel ν π n h, π.select n h {z.1} ≠ 0 := by
  have hm : MeasurableSet {z : Fin K × ℝ | π.select n h {z.1} ≠ 0} := by
    exact ((measurable_of_countable (fun a => π.select n h {a})).comp measurable_fst)
      (measurableSet_singleton 0).compl
  rw [banditStepKernel]
  apply Kernel.ae_compProd_of_ae_ae hm
  apply (ae_iff_of_countable).2
  intro a ha
  exact ae_of_all _ (fun _ => ha)

lemma trajectory_policy_atoms {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) :
    ∀ᵐ ω ∂banditTrajMeasure ν π, ∀ t, π.select t (banditTrajPrefix K t ω) {(ω t).1} ≠ 0 := by
  apply ae_all_iff.mpr
  intro t
  cases t with
  | zero =>
    let μ₀ := banditStepKernel ν π 0 (fun i : Fin 0 => i.elim0)
    have hi : ∀ᵐ h ∂μ₀.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Fin K × ℝ)).symm,
        π.select 0 (fun i : Fin 0 => i.elim0) {(h ⟨0,by simp⟩).1} ≠ 0 := by
      have hm : MeasurableSet {h : Finset.Iic 0 → Fin K × ℝ |
          π.select 0 (fun i : Fin 0 => i.elim0) {(h ⟨0,by simp⟩).1} ≠ 0} :=
        ((measurable_of_countable (fun a => π.select 0 (fun i : Fin 0 => i.elim0) {a})).comp
          (measurable_fst.comp (measurable_pi_apply _))) (measurableSet_singleton 0).compl
      apply (ae_map_iff (MeasurableEquiv.piUnique _).symm.measurable.aemeasurable hm).2
      exact step_support ν π _
    have hp := initial_prefix_law μ₀ (banditTrajKernel ν π)
    rw [← hp] at hi
    have hh := ae_of_ae_map (measurable_frestrictLe 0).aemeasurable hi
    filter_upwards [hh] with ω hω
    have hempty : banditTrajPrefix K 0 ω = (fun i : Fin 0 => i.elim0) := Subsingleton.elim _ _
    rw [hempty]
    exact hω
  | succ t =>
    let P := banditTrajMeasure ν π
    let Q := P.map (frestrictLe t)
    have hm : MeasurableSet {p : (Finset.Iic t → Fin K × ℝ) × (Fin K × ℝ) |
        π.select (t+1) (banditIicHistory K t p.1) {p.2.1} ≠ 0} := by
      exact ((selectAtom_measurable π).comp
        ((measurable_banditIicHistory.comp measurable_fst).prodMk
          (measurable_fst.comp measurable_snd)))
            (measurableSet_singleton 0).compl
    have hh : ∀ᵐ p ∂Q ⊗ₘ banditTrajKernel ν π t,
        π.select (t+1) (banditIicHistory K t p.1) {p.2.1} ≠ 0 := by
      apply Measure.ae_compProd_of_ae_ae hm
      exact ae_of_all _ (fun h => step_support ν π (banditIicHistory K t h))
    have hjoint : Q ⊗ₘ banditTrajKernel ν π t =
        P.map (fun ω => (frestrictLe t ω, ω (t+1))) :=
      Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    rw [hjoint] at hh
    exact ae_of_ae_map (f := fun ω : ℕ → Fin K × ℝ => (frestrictLe t ω, ω (t+1)))
      (by fun_prop) hh

lemma trajectory_follows_allowed {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K)
    (allowed : (t : ℕ) → BanditHistory K t → Set (Fin K))
    (hall : ∀ t h, π.select t h (allowed t h)ᶜ=0) :
    ∀ᵐ ω ∂banditTrajMeasure ν π, ∀ t, (ω t).1 ∈ allowed t (banditTrajPrefix K t ω) := by
  filter_upwards [trajectory_policy_atoms ν π] with ω hω
  intro t
  by_contra h
  apply hω t
  exact measure_mono_null (Set.singleton_subset_iff.mpr h) (hall t _)

lemma policy_follows_C {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K)
    (wt : (Fin K → ℝ) → (Fin K → ℝ)) (hπ : IsCTrackingPolicy wt π) :
    ∀ᵐ ω ∂banditTrajMeasure ν π, FollowsCTracking wt ω := by
  obtain ⟨wp,hwp,hall⟩ := hπ
  filter_upwards [trajectory_follows_allowed ν π (fun _ h => allowedC wp h) hall] with ω hω
  exact ⟨wp,hwp,hω⟩

lemma policy_follows_D {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K)
    (wt : (Fin K → ℝ) → (Fin K → ℝ)) (hπ : IsDTrackingPolicy wt π) :
    ∀ᵐ ω ∂banditTrajMeasure ν π, FollowsDTracking wt ω :=
  trajectory_follows_allowed ν π (fun _ h => allowedD wt h) hπ

end OptimalBAI.TrackStop

/- Reused from accepted submission b79181f4-ce0e-48e3-b41f-ee2a40ee2dfb. -/

open scoped BigOperators
open BanditAlgorithm OptimalBAI.TrackStop

private theorem cumulative_tracking {K : ℕ} (hK : 0 < K) (n : ℕ) (hn : 0 < n)
    (p : ℕ → Fin K → ℝ)
    (hp : ∀ k, 1 ≤ k → k ≤ n → (∀ a, 0 ≤ p k a) ∧ ∑ a, p k a = 1)
    (N : ℕ → Fin K → ℝ) (I : ℕ → Fin K)
    (hN0 : N 0 = 0)
    (hI : ∀ k, k < n → ∀ i : Fin K,
      (∑ j ∈ Finset.Icc 1 (k + 1), p j i) - N k i ≤
        (∑ j ∈ Finset.Icc 1 (k + 1), p j (I (k + 1))) - N k (I (k + 1)))
    (hN : ∀ k, k < n → N (k + 1) = N k + Pi.single (I (k + 1)) (1 : ℝ)) :
    ∀ i : Fin K, |N n i - ∑ j ∈ Finset.Icc 1 n, p j i| ≤ (K : ℝ) - 1 := by
  let P : ℕ → Fin K → ℝ := fun k i => ∑ j ∈ Finset.Icc 1 k, p j i
  have hP0 : ∀ i, P 0 i = 0 := by simp [P]
  have hPstep : ∀ k i, P (k+1) i = P k i + p (k+1) i := by
    intro k i
    dsimp [P]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k+1)]
  have hPsum : ∀ k, k ≤ n → ∑ i, P k i = (k : ℝ) := by
    intro k
    induction k with
    | zero => simp [P]
    | succ k ih =>
      intro hk
      simp_rw [hPstep]
      rw [Finset.sum_add_distrib, ih (by omega), (hp (k+1) (by omega) hk).2]
      simp
  have hNsum : ∀ k, k ≤ n → ∑ i, N k i = (k : ℝ) := by
    intro k
    induction k with
    | zero => simp [hN0]
    | succ k ih =>
      intro hk
      rw [hN k (by omega)]
      simp only [Pi.add_apply, Finset.sum_add_distrib]
      rw [ih (by omega)]
      simp
  have hu : ∀ k, k ≤ n → ∀ i, N k i - P k i ≤ 1 := by
    intro k
    induction k with
    | zero => simp [hN0, hP0]
    | succ k ih =>
      intro hk i
      have hk' : k < n := by omega
      have hs : ∑ a, (P (k+1) a - N k a) = 1 := by
        rw [Finset.sum_sub_distrib, hPsum (k+1) hk, hNsum k (by omega)]
        push_cast
        ring
      have hbest : 0 ≤ P (k+1) (I (k+1)) - N k (I (k+1)) := by
        by_contra hh
        have hneg : P (k+1) (I (k+1)) - N k (I (k+1)) < 0 := lt_of_not_ge hh
        have hall : ∑ a, (P (k+1) a - N k a) ≤ 0 :=
          Finset.sum_nonpos (fun a _ => (hI k hk' a).trans hneg.le)
        linarith
      by_cases hi : i = I (k+1)
      · subst i
        rw [hN k hk']
        simp only [Pi.add_apply, Pi.single_eq_same]
        linarith
      · have hprev := ih (by omega) i
        have hpi := (hp (k+1) (by omega) hk).1 i
        rw [hN k hk', hPstep]
        simp only [Pi.add_apply, Pi.single_apply, if_neg hi, add_zero]
        linarith
  have hz : ∑ i, (N n i - P n i) = 0 := by
    rw [Finset.sum_sub_distrib, hNsum n le_rfl, hPsum n le_rfl, sub_self]
  intro i
  have hlow : -((K : ℝ)-1) ≤ N n i - P n i := by
    have he := Finset.sum_erase_add Finset.univ (fun a => N n a - P n a)
      (Finset.mem_univ i)
    have hbound : ∑ a ∈ Finset.univ.erase i, (N n a - P n a) ≤
        ∑ _a ∈ Finset.univ.erase i, (1 : ℝ) :=
      Finset.sum_le_sum (fun a _ => hu n le_rfl a)
    have hc : (∑ _a ∈ Finset.univ.erase i, (1 : ℝ)) = (K : ℝ)-1 := by
      simp [Finset.card_erase_of_mem, Nat.cast_sub (Nat.succ_le_of_lt hK)]
    rw [hc] at hbound
    rw [hz] at he
    linarith
  have hu' : N n i - P n i ≤ (K : ℝ)-1 := by
    by_cases hK1 : K = 1
    · subst K
      have hi : i = 0 := Subsingleton.elim _ _
      simpa [hi] using le_of_eq hz
    · have hk2 : (2 : ℝ) ≤ K := by exact_mod_cast (show 2 ≤ K by omega)
      linarith [hu n le_rfl i]
  exact abs_le.mpr ⟨hlow, hu'⟩

private theorem eps_bounds {K : ℕ} (hK : 0 < K) (s : ℕ) :
    0 < cEps K s ∧ cEps K s ≤ 1/(K:ℝ) ∧
    Real.sqrt ((K:ℝ)^2+(s:ℝ)+1)-Real.sqrt ((K:ℝ)^2+(s:ℝ)) ≤ cEps K s ∧
    cEps K s ≤ Real.sqrt ((s:ℝ)+1)-Real.sqrt (s:ℝ) := by
  have hKr : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0:ℝ) < K := by positivity
  have hs : (0:ℝ) ≤ s := by positivity
  have hsq : (0:ℝ) < (K:ℝ)^2+(s:ℝ) := by positivity
  have hr : 0 < Real.sqrt ((K:ℝ)^2+(s:ℝ)) := Real.sqrt_pos.mpr hsq
  have hr2 := Real.sq_sqrt hsq.le
  have hn2 := Real.sq_sqrt (show 0 ≤ (K:ℝ)^2+(s:ℝ)+1 by positivity)
  have hs2 := Real.sq_sqrt hs
  have hs12 := Real.sq_sqrt (show 0 ≤ (s:ℝ)+1 by positivity)
  have hrK : (K:ℝ) ≤ Real.sqrt ((K:ℝ)^2+(s:ℝ)) := by nlinarith
  have hmon : Real.sqrt ((K:ℝ)^2+(s:ℝ)) ≤ Real.sqrt ((K:ℝ)^2+(s:ℝ)+1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hdiff : 0 ≤ Real.sqrt ((K:ℝ)^2+(s:ℝ)+1)-Real.sqrt ((K:ℝ)^2+(s:ℝ)) := sub_nonneg.mpr hmon
  have hdiff2 : 0 ≤ Real.sqrt ((s:ℝ)+1)-Real.sqrt (s:ℝ) := sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hsup1 : Real.sqrt ((s:ℝ)+1) ≤ Real.sqrt ((K:ℝ)^2+(s:ℝ)) := Real.sqrt_le_sqrt (by nlinarith)
  have hsup0 : Real.sqrt (s:ℝ) ≤ Real.sqrt ((K:ℝ)^2+(s:ℝ)) := Real.sqrt_le_sqrt (by nlinarith)
  dsimp [cEps]
  refine ⟨by positivity,?_,?_,?_⟩
  · apply (one_div_le_one_div (by positivity) hKpos).2
    linarith
  · apply (le_div_iff₀ (by positivity : 0 < 2*Real.sqrt ((K:ℝ)^2+(s:ℝ)))).mpr
    nlinarith [mul_nonneg hdiff hdiff]
  · apply (div_le_iff₀ (by positivity : 0 < 2*Real.sqrt ((K:ℝ)^2+(s:ℝ)))).mpr
    nlinarith [mul_nonneg hdiff2 (sub_nonneg.mpr hsup1),mul_nonneg hdiff2 (sub_nonneg.mpr hsup0)]

private theorem eps_sums {K : ℕ} (hK : 0 < K) (t : ℕ) :
    Real.sqrt ((K:ℝ)^2+(t:ℝ))-(K:ℝ) ≤ ∑ s ∈ Finset.range t,cEps K s ∧
    ∑ s ∈ Finset.range t,cEps K s ≤ Real.sqrt (t:ℝ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have he := eps_bounds hK t
    rw [Finset.sum_range_succ]
    push_cast
    simp only [← add_assoc]
    constructor <;> linarith [he.2.2.1,he.2.2.2]

private theorem projection_distance {K : ℕ} (hK : 0 < K)
    (wt : (Fin K → ℝ) → Fin K → ℝ) (hwt : ∀ μ,wt μ ∈ simplex K)
    (wp : ℝ → (Fin K → ℝ) → Fin K → ℝ) (hp : IsLinftyProjection K wt wp)
    (ε : ℝ) (he : 0 < ε) (heK : ε ≤ 1/(K:ℝ)) (μ : Fin K → ℝ) (a : Fin K) :
    |wp ε μ a-wt μ a| ≤ (K:ℝ)*ε := by
  have hKr : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0:ℝ) < K := by positivity
  have hKe : (K:ℝ)*ε ≤ 1 := by nlinarith [(le_div_iff₀ hKpos).mp heK]
  have hcoef : 0 ≤ 1-(K:ℝ)*ε := by linarith
  have hw : (∀ a,0 ≤ wt μ a) ∧ ∑ a,wt μ a=1 := hwt μ
  have hw1 (a : Fin K) : wt μ a ≤ 1 := by
    rw [← hw.2]
    exact Finset.single_le_sum (fun b _ => hw.1 b) (Finset.mem_univ a)
  let v : Fin K → ℝ := fun b => (1-(K:ℝ)*ε)*wt μ b+ε
  have hv : v ∈ simplexEps K ε := by
    constructor
    · intro b
      dsimp [v]
      constructor
      · nlinarith [mul_nonneg hcoef (hw.1 b)]
      · nlinarith [mul_le_mul_of_nonneg_left (hw1 b) hcoef]
    · simp [v,Finset.sum_add_distrib,← Finset.mul_sum,hw.2]
  have hnorm : ‖v-wt μ‖ ≤ (K:ℝ)*ε := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro b
    simp only [Pi.sub_apply,Real.norm_eq_abs]
    rw [abs_le]
    dsimp [v]
    have hh := mul_le_mul_of_nonneg_left (hw1 b) (by positivity : 0 ≤ (K:ℝ)*ε)
    have hn := mul_nonneg (show 0 ≤ (K:ℝ)*ε by positivity) (hw.1 b)
    have heK1 := mul_le_mul_of_nonneg_right hKr he.le
    constructor <;> nlinarith
  have hpdist := le_trans ((hp ε he heK μ).2 v hv) hnorm
  exact (pi_norm_le_iff_of_nonneg (by positivity)).mp hpdist a

private theorem prefix_count {K : ℕ} (ω : ℕ → Fin K × ℝ) (t : ℕ) (a : Fin K) :
    armPullCount a (banditTrajPrefix K t ω) = trajPullCount a t ω := by
  classical
  unfold armPullCount
  rw [Set.toFinset_ofPred,Finset.card_filter]
  unfold trajPullCount
  rw [Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if (ω i).1=a then 1 else 0) t

private theorem prefix_mean {K : ℕ} (ω : ℕ → Fin K × ℝ) (t : ℕ) (a : Fin K) :
    armEmpiricalMean a (banditTrajPrefix K t ω) = trajEmpiricalMean a t ω := by
  classical
  unfold armEmpiricalMean
  rw [Set.toFinset_ofPred,Finset.sum_filter,prefix_count]
  unfold trajEmpiricalMean
  rw [Finset.sum_filter]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => if (ω i).1=a then (ω i).2 else 0) t

private theorem hist_mean_prefix {K : ℕ} (ω : ℕ → Fin K × ℝ) (t s : ℕ) (hs : s ≤ t) :
    histMeanAt (banditTrajPrefix K t ω) s = trajMeanVec s ω := by
  ext a
  dsimp [histMeanAt,trajMeanVec]
  have he : (fun i : Fin (min s t) => banditTrajPrefix K t ω (Fin.castLE (Nat.min_le_right s t) i)) = banditTrajPrefix K (min s t) ω := rfl
  rw [he,prefix_mean,Nat.min_eq_left hs]

private theorem count_step {K : ℕ} (ω : ℕ → Fin K × ℝ) (t : ℕ) (a : Fin K) :
    (trajPullCount a (t+1) ω : ℝ) = (trajPullCount a t ω : ℝ) + if a=(ω t).1 then 1 else 0 := by
  simp only [trajPullCount,Finset.range_add_one,Finset.filter_insert]
  by_cases ha : a=(ω t).1
  · simp [ha,Finset.mem_filter,Finset.mem_range]
  · simp [ha,Ne.symm ha]

private theorem shifted_sum (p : ℕ → ℝ) (t : ℕ) :
    ∑ j ∈ Finset.Icc 1 t,p (j-1) = ∑ j ∈ Finset.range t,p j := by
  rw [← Finset.Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
  simp

theorem c_tracking_bounds_reused {K : ℕ} (wt : (Fin K → ℝ) → (Fin K → ℝ))
    (hwt_simplex : ∀ μ', wt μ' ∈ simplex K)
    (ω : ℕ → Fin K × ℝ) (hω : FollowsCTracking wt ω) :
    ∀ t : ℕ, 1 ≤ t → ∀ a : Fin K,
      Real.sqrt ((t : ℝ) + (K : ℝ) ^ 2) - 2 * (K : ℝ) ≤ (trajPullCount a t ω : ℝ) ∧
      |(trajPullCount a t ω : ℝ) - ∑ s ∈ Finset.range t, wt (trajMeanVec s ω) a| ≤
        (K : ℝ) * (1 + Real.sqrt (t : ℝ)) := by
  classical
  obtain ⟨wp,hwp,hsel⟩ := hω
  have hK : 0 < K := Nat.lt_of_le_of_lt (Nat.zero_le _) (ω 0).1.isLt
  have hpt : ∀ j, wp (cEps K j) (trajMeanVec j ω) ∈ simplexEps K (cEps K j) := by
    intro j
    exact (hwp _ (eps_bounds hK j).1 (eps_bounds hK j).2.1 _).1
  intro t ht a
  have hc := cumulative_tracking hK t ht
    (fun j => wp (cEps K (j-1)) (trajMeanVec (j-1) ω))
    (fun j _ _ => ⟨fun b => le_trans (eps_bounds hK (j-1)).1.le ((hpt (j-1)).1 b).1,(hpt (j-1)).2⟩)
    (fun k b => (trajPullCount b k ω : ℝ)) (fun j => (ω (j-1)).1)
    (by ext b; simp [trajPullCount]) ?_ ?_ a
  · rw [shifted_sum (fun j => wp (cEps K j) (trajMeanVec j ω) a)] at hc
    have hlp : ∑ s ∈ Finset.range t,cEps K s ≤
        ∑ s ∈ Finset.range t,wp (cEps K s) (trajMeanVec s ω) a := by
      apply Finset.sum_le_sum
      intro s _
      exact ((hpt s).1 a).1
    have hd : |(∑ s ∈ Finset.range t,wp (cEps K s) (trajMeanVec s ω) a)-
        ∑ s ∈ Finset.range t,wt (trajMeanVec s ω) a| ≤ (K:ℝ)*Real.sqrt (t:ℝ) := by
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ s ∈ Finset.range t,|wp (cEps K s) (trajMeanVec s ω) a-wt (trajMeanVec s ω) a| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ s ∈ Finset.range t,(K:ℝ)*cEps K s := by
          apply Finset.sum_le_sum
          intro s _
          exact projection_distance hK wt hwt_simplex wp hwp _ (eps_bounds hK s).1 (eps_bounds hK s).2.1 _ a
        _ ≤ (K:ℝ)*Real.sqrt (t:ℝ) := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (eps_sums hK t).2 (by positivity)
    constructor
    · have he := (eps_sums hK t).1
      rw [add_comm ((K:ℝ)^2) (t:ℝ)] at he
      have hh := (abs_le.mp hc).1
      linarith
    · have hh := abs_add_le ((trajPullCount a t ω : ℝ)-∑ s ∈ Finset.range t,wp (cEps K s) (trajMeanVec s ω) a)
        ((∑ s ∈ Finset.range t,wp (cEps K s) (trajMeanVec s ω) a)-∑ s ∈ Finset.range t,wt (trajMeanVec s ω) a)
      simp only [sub_add_sub_cancel] at hh
      linarith
  · intro k hk b
    have htar (b : Fin K) : cTarget wp (banditTrajPrefix K k ω) b =
        ∑ s ∈ Finset.range (k+1),wp (cEps K s) (trajMeanVec s ω) b := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hist_mean_prefix ω k s (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hs)]
    have hh := hsel k b
    change cTarget wp (banditTrajPrefix K k ω) b-(armPullCount b (banditTrajPrefix K k ω):ℝ) ≤
      cTarget wp (banditTrajPrefix K k ω) (ω k).1-(armPullCount (ω k).1 (banditTrajPrefix K k ω):ℝ) at hh
    rw [htar,htar,prefix_count,prefix_count] at hh
    simp only [Nat.add_sub_cancel]
    rw [shifted_sum (fun j => wp (cEps K j) (trajMeanVec j ω) b),
      shifted_sum (fun j => wp (cEps K j) (trajMeanVec j ω) (ω k).1)]
    exact hh
  · intro k hk
    ext b
    simp only [Pi.add_apply,Nat.add_sub_cancel,Pi.single_apply]
    simpa [eq_comm] using count_step ω k b


/- Reused from accepted submission fc848517-a37c-4820-ab51-0a5501c47bf8. -/
open scoped BigOperators
open BanditAlgorithm OptimalBAI.TrackStop
namespace DTrackProof
private theorem forced_lower {K : ℕ} (hK : 2 ≤ K) (N : ℕ → Fin K → ℕ) (I : ℕ → Fin K)
    (hstep : ∀ t a, N (t+1) a = N t a + if a = I t then 1 else 0)
    (hsel : ∀ (t : ℕ) a, (N t a : ℝ) < Real.sqrt (t : ℝ) - (K : ℝ)/2 → N t (I t) ≤ N t a) :
    ∀ (t : ℕ) a, max (Real.sqrt (t : ℝ)-(K : ℝ)/2) 0 - 1 ≤ (N t a : ℝ) := by
  classical
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hmono : ∀ a, Monotone (fun t => N t a) := fun a => monotone_nat_of_le_succ fun t => by
    rw [hstep]; omega
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro a
    by_contra! hbad
    let q := N t a
    have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
    have hbad' : (q : ℝ)+1 < Real.sqrt (t : ℝ)-(K : ℝ)/2 := by
      have hmax := (lt_max_iff.mp (show (q : ℝ)+1 < max (Real.sqrt (t : ℝ)-(K : ℝ)/2) 0 by linarith))
      rcases hmax with ht | ht
      · exact ht
      · linarith
    have hsqt := Real.sq_sqrt (Nat.cast_nonneg t)
    have htK : K ≤ t := by
      have : (K : ℝ) < t := by nlinarith [sq_nonneg ((K : ℝ)/2)]
      exact_mod_cast this.le
    let u := t-K
    have hu : u < t := by dsimp [u]; omega
    have hu_cast : (u : ℝ) = (t : ℝ)-(K : ℝ) := by dsimp [u]; exact Nat.cast_sub htK
    have hsqu := Real.sq_sqrt (Nat.cast_nonneg u)
    have hsqrt : Real.sqrt (t : ℝ)-1 < Real.sqrt (u : ℝ) := by
      apply (sq_lt_sq₀ (by linarith : 0 ≤ Real.sqrt (t : ℝ)-1) (Real.sqrt_nonneg _)).mp
      rw [hsqu, hu_cast]
      nlinarith
    have huq : (q : ℝ) < Real.sqrt (u : ℝ)-(K : ℝ)/2 := by linarith
    have hbase : ∀ b, q ≤ N u b := by
      intro b
      have hh := ih u hu b
      have hm := le_max_left (Real.sqrt (u : ℝ)-(K : ℝ)/2) 0
      have hc : (q : ℝ) < (N u b : ℝ)+1 := by linarith
      have hc' : q < N u b+1 := by exact_mod_cast hc
      omega
    have hchoose : ∀ j, u ≤ j → j < t → N j (I j) = q := by
      intro j hj hjt
      have hja : N j a ≤ q := hmono a hjt.le
      have ht : (N j a : ℝ) < Real.sqrt (j : ℝ)-(K : ℝ)/2 := by
        have hsj := Real.sqrt_le_sqrt (show (u : ℝ) ≤ j by exact_mod_cast hj)
        have hjr : (N j a : ℝ) ≤ q := by exact_mod_cast hja
        linarith
      exact le_antisymm ((hsel j a ht).trans hja) ((hbase (I j)).trans (hmono (I j) hj))
    let S : ℕ → ℕ := fun j => ∑ b, min (N j b) (q+1)
    have hSstep : ∀ j, u ≤ j → j < t → S (j+1) = S j+1 := by
      intro j hj hjt
      have he : ∀ b, min (N (j+1) b) (q+1) = min (N j b) (q+1) + if b = I j then 1 else 0 := by
        intro b
        rw [hstep]
        by_cases hb : b = I j
        · subst b; rw [hchoose j hj hjt]; simp
        · simp [hb]
      dsimp only [S]
      simp_rw [he]
      rw [Finset.sum_add_distrib]
      simp
    have hSeq : ∀ j, u ≤ j → j ≤ t → S j = S u+(j-u) := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => simp
      | succ j hj ih =>
        intro hjt
        rw [hSstep j hj (by omega), ih (by omega)]
        omega
    have hSlower : K*q ≤ S u := by
      calc K*q = ∑ _b : Fin K, q := by simp
           _ ≤ S u := Finset.sum_le_sum (fun b _ => le_min (hbase b) (by omega))
    have hSupper : S t < K*(q+1) := by
      calc S t < ∑ _b : Fin K, (q+1) := by
             dsimp only [S]
             apply Finset.sum_lt_sum (fun b _ => min_le_right _ _)
             refine ⟨a, Finset.mem_univ a, ?_⟩
             dsimp only [q]; omega
           _ = K*(q+1) := by simp
    have htS := hSeq t (by dsimp [u]; omega) le_rfl
    have htu : t-u = K := by dsimp [u]; omega
    rw [htu] at htS
    nlinarith
private theorem sqrt_small (ε : ℝ) (hε : 0 < ε) (T : ℕ) (hT : 1/ε^2 ≤ (T : ℝ))
    (t : ℕ) (ht : T ≤ t) : Real.sqrt (t : ℝ) ≤ ε*(t : ℝ) := by
  have he : ε^2 ≠ 0 := pow_ne_zero _ hε.ne'
  have hmul : 1 ≤ ε^2*(t : ℝ) := by
    have hh : 1/ε^2 ≤ (t : ℝ) := hT.trans (by exact_mod_cast ht)
    exact (div_le_iff₀ (sq_pos_of_pos hε)).mp hh |>.trans_eq (mul_comm _ _)
  have hs := Real.sq_sqrt (Nat.cast_nonneg t)
  have heq : (ε*Real.sqrt (t : ℝ))^2 = ε^2*(t : ℝ) := by rw [mul_pow, hs]
  have h1 : 1 ≤ ε*Real.sqrt (t : ℝ) := by
    have hn : 0 ≤ ε*Real.sqrt (t : ℝ) := by positivity
    nlinarith
  have hh := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg (t : ℝ))
  nlinarith
private theorem tracking_upper {K : ℕ} (N : ℕ → Fin K → ℕ) (I : ℕ → Fin K)
    (hstep : ∀ t a, N (t+1) a = N t a + if a = I t then 1 else 0)
    (hsum : ∀ t, ∑ a, N t a = t)
    (w : Fin K → ℝ) (hw : ∀ a, 0 ≤ w a) (ε : ℝ) (hε : 0 < ε)
    (T : ℕ) (hT : 1 ≤ T)
    (hsel : ∀ t, T ≤ t → (N t (I t) : ℝ) ≤ (t : ℝ)*(w (I t)+ε)) :
    ∀ t, T ≤ t → ∀ a, (N t a : ℝ) ≤ (t : ℝ)*(w a+ε)+(T : ℝ) := by
  classical
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    intro a
    have ha : N T a ≤ T := (Finset.single_le_sum (fun b _ => Nat.zero_le (N T b)) (Finset.mem_univ a)).trans_eq (hsum T)
    have har : (N T a : ℝ) ≤ T := by exact_mod_cast ha
    have hh : 0 ≤ (T : ℝ)*(w a+ε) := mul_nonneg (Nat.cast_nonneg _) (add_nonneg (hw a) hε.le)
    linarith
  | succ t ht ih =>
    intro a
    rw [hstep]
    by_cases ha : a = I t
    · subst a; rw [if_pos rfl, Nat.cast_add, Nat.cast_one, Nat.cast_add, Nat.cast_one]
      have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
      nlinarith [hsel t ht, hw (I t)]
    · rw [if_neg ha, add_zero, Nat.cast_add, Nat.cast_one]
      nlinarith [ih a, hw a]
private theorem simplex_error {K : ℕ} (hK : 2 ≤ K) (v w : Fin K → ℝ)
    (hs : ∑ a, v a = ∑ a, w a) (ε : ℝ) (hε : 0 < ε)
    (hu : ∀ a, v a-w a ≤ 2*ε) : ∀ a, |v a-w a| ≤ 3*((K : ℝ)-1)*ε := by
  classical
  have hsum : ∑ a, (v a-w a) = 0 := by rw [Finset.sum_sub_distrib, hs, sub_self]
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  intro a
  have he := Finset.sum_erase_add Finset.univ (fun b => v b-w b) (Finset.mem_univ a)
  have hb : ∑ b ∈ Finset.univ.erase a, (v b-w b) ≤ ∑ _b ∈ Finset.univ.erase a, 2*ε :=
    Finset.sum_le_sum fun b _ => hu b
  have hc : (∑ _b ∈ Finset.univ.erase a, 2*ε) = ((K : ℝ)-1)*(2*ε) := by
    simp [Finset.card_erase_of_mem, Nat.cast_sub (by omega : 1 ≤ K)]
  rw [hc] at hb
  rw [hsum] at he
  apply abs_le.mpr
  constructor <;> nlinarith [hu a, mul_nonneg (by linarith : 0 ≤ (K : ℝ)-1) hε.le]

private theorem prefix_count {K : ℕ} (ω : ℕ → Fin K × ℝ) (t : ℕ) (a : Fin K) :
    armPullCount a (banditTrajPrefix K t ω) = trajPullCount a t ω := by
  classical
  unfold armPullCount
  rw [Set.toFinset_ofPred,Finset.card_filter]
  unfold trajPullCount
  rw [Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if (ω i).1=a then 1 else 0) t

private theorem prefix_mean {K : ℕ} (ω : ℕ → Fin K × ℝ) (t : ℕ) (a : Fin K) :
    armEmpiricalMean a (banditTrajPrefix K t ω) = trajEmpiricalMean a t ω := by
  classical
  unfold armEmpiricalMean
  rw [Set.toFinset_ofPred,Finset.sum_filter,prefix_count]
  unfold trajEmpiricalMean
  rw [Finset.sum_filter]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => if (ω i).1=a then (ω i).2 else 0) t

private theorem hist_mean_prefix {K : ℕ} (ω : ℕ → Fin K × ℝ) (t s : ℕ) (hs : s ≤ t) :
    histMeanAt (banditTrajPrefix K t ω) s = trajMeanVec s ω := by
  ext a
  dsimp [histMeanAt,trajMeanVec]
  have he : (fun i : Fin (min s t) => banditTrajPrefix K t ω (Fin.castLE (Nat.min_le_right s t) i)) = banditTrajPrefix K (min s t) ω := rfl
  rw [he,prefix_mean,Nat.min_eq_left hs]

private theorem count_step {K : ℕ} (ω : ℕ → Fin K × ℝ) (t : ℕ) (a : Fin K) :
    trajPullCount a (t+1) ω = trajPullCount a t ω + if a=(ω t).1 then 1 else 0 := by
  simp only [trajPullCount,Finset.range_add_one,Finset.filter_insert]
  by_cases ha : a=(ω t).1
  · simp [ha,Finset.mem_filter,Finset.mem_range]
  · simp [ha,Ne.symm ha]


private theorem count_sum {K : ℕ} (ω : ℕ → Fin K × ℝ) (t : ℕ) :
    ∑ a, trajPullCount a t ω = t := by
  induction t with
  | zero => simp [trajPullCount]
  | succ t ih => simp_rw [count_step]; rw [Finset.sum_add_distrib, ih]; simp
private theorem forced_choice {K : ℕ} (wt : (Fin K → ℝ) → Fin K → ℝ)
    (ω : ℕ → Fin K × ℝ) (hω : FollowsDTracking wt ω) (t : ℕ) (a : Fin K)
    (ha : (trajPullCount a t ω : ℝ) < Real.sqrt (t : ℝ)-(K : ℝ)/2) :
    trajPullCount (ω t).1 t ω ≤ trajPullCount a t ω := by
  have ham : a ∈ forcedSet (banditTrajPrefix K t ω) := by
    change (armPullCount a (banditTrajPrefix K t ω) : ℝ) < _
    simpa only [prefix_count] using ha
  rcases hω t with ⟨_, _, hmin⟩ | ⟨hem, _⟩
  · simpa only [prefix_count] using hmin a ham
  · rw [hem] at ham; exact False.elim ham
private theorem chosen_upper {K : ℕ} (wt : (Fin K → ℝ) → Fin K → ℝ)
    (hwt : ∀ μ, wt μ ∈ simplex K)
    (ω : ℕ → Fin K × ℝ) (hω : FollowsDTracking wt ω) (t : ℕ) :
    (trajPullCount (ω t).1 t ω : ℝ) ≤ max (Real.sqrt (t : ℝ)) ((t : ℝ)*wt (trajMeanVec t ω) (ω t).1) := by
  rcases hω t with ⟨_, hmem, _⟩ | ⟨_, hmax⟩
  · change (armPullCount (ω t).1 (banditTrajPrefix K t ω) : ℝ) < _ at hmem
    rw [prefix_count] at hmem
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    exact (by linarith : (trajPullCount (ω t).1 t ω : ℝ) ≤ Real.sqrt (t : ℝ)).trans (le_max_left _ _)
  · simp only [prefix_count, hist_mean_prefix ω t t le_rfl] at hmax
    have hsum : ∑ b, ((t : ℝ)*wt (trajMeanVec t ω) b - (trajPullCount b t ω : ℝ)) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, (hwt _).2]
      have hc : (∑ b, (trajPullCount b t ω : ℝ)) = (t : ℝ) := by exact_mod_cast count_sum ω t
      rw [hc]; ring
    have hn : 0 ≤ (t : ℝ)*wt (trajMeanVec t ω) (ω t).1 - (trajPullCount (ω t).1 t ω : ℝ) := by
      by_contra! hh
      have hneg : (∑ b, ((t : ℝ)*wt (trajMeanVec t ω) b - (trajPullCount b t ω : ℝ))) < ∑ _b : Fin K, (0 : ℝ) := by
        apply Finset.sum_lt_sum (fun b _ => (hmax b).trans hh.le)
        exact ⟨(ω t).1, Finset.mem_univ _, hh⟩
      simp only [hsum, Finset.sum_const_zero] at hneg
      linarith
    have hbound : (trajPullCount (ω t).1 t ω : ℝ) ≤ (t : ℝ)*wt (trajMeanVec t ω) (ω t).1 := by linarith
    exact hbound.trans (le_max_right _ _)
private theorem uniform_tracking {K : ℕ} (hK : 2 ≤ K) (w : Fin K → ℝ) (hw : w ∈ simplex K)
    (wt : (Fin K → ℝ) → Fin K → ℝ) (hwt : ∀ μ, wt μ ∈ simplex K)
    (ε : ℝ) (hε : 0 < ε) (t₀ : ℕ) : ∃ tε : ℕ, t₀ ≤ tε ∧
    ∀ ω : ℕ → Fin K × ℝ, FollowsDTracking wt ω →
      (∀ t, t₀ ≤ t → ∀ a, |wt (trajMeanVec t ω) a-w a| ≤ ε) →
      ∀ t, tε ≤ t → ∀ a, |(trajPullCount a t ω : ℝ)/(t : ℝ)-w a| ≤ 3*((K : ℝ)-1)*ε := by
  obtain ⟨T₁,hT₁⟩ := exists_nat_gt (1/ε^2)
  let T := max t₀ (max 1 T₁)
  have hT0 : t₀ ≤ T := le_max_left _ _
  have hT1 : 1 ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hT2 : T₁ ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  have hTr : 1/ε^2 ≤ (T : ℝ) := hT₁.le.trans (by exact_mod_cast hT2)
  obtain ⟨T₂,hT₂⟩ := exists_nat_gt ((T : ℝ)/ε)
  refine ⟨max T T₂, hT0.trans ((le_max_left _ _)), ?_⟩
  intro ω hω hclose
  have hsel : ∀ t, T ≤ t → (trajPullCount (ω t).1 t ω : ℝ) ≤ (t : ℝ)*(w (ω t).1+ε) := by
    intro t ht
    apply (chosen_upper wt hwt ω hω t).trans
    apply max_le
    · have hh := sqrt_small ε hε T hTr t ht
      have hw0 := hw.1 (ω t).1
      nlinarith [Nat.cast_nonneg (α := ℝ) t]
    · have hh := (abs_le.mp (hclose t (hT0.trans ht) (ω t).1)).2
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have hub := tracking_upper (fun t a => trajPullCount a t ω) (fun t => (ω t).1)
    (count_step ω) (count_sum ω) w hw.1 ε hε T hT1 hsel
  intro t ht
  have hTt : T ≤ t := (le_max_left _ _).trans ht
  have hT₂t : T₂ ≤ t := (le_max_right _ _).trans ht
  have htp : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hterr : (T : ℝ) ≤ ε*(t : ℝ) := by
    have hh : (T : ℝ)/ε ≤ (t : ℝ) := hT₂.le.trans (by exact_mod_cast hT₂t)
    have hh' := (div_le_iff₀ hε).mp hh
    nlinarith
  have hsum : (∑ a, (trajPullCount a t ω : ℝ)/(t : ℝ)) = ∑ a, w a := by
    rw [← Finset.sum_div, hw.2]
    have hc : (∑ b, (trajPullCount b t ω : ℝ)) = (t : ℝ) := by exact_mod_cast count_sum ω t
    rw [hc, div_self htp.ne']
  apply simplex_error hK (fun a => (trajPullCount a t ω : ℝ)/(t : ℝ)) w hsum ε hε
  intro a
  have hh := (div_le_iff₀ htp).mpr (show (trajPullCount a t ω : ℝ) ≤ (w a+2*ε)*(t : ℝ) by nlinarith [hub t hTt a])
  linarith

end DTrackProof

theorem d_tracking_bounds_reused (F : ExpFamily) {K : ℕ} (hK : 2 ≤ K)
    (μ : Fin K → ℝ) (hμ : μ ∈ bestArmMeans F K) (w : Fin K → ℝ) (hw : IsOptimalProportion F μ w)
    (wt : (Fin K → ℝ) → (Fin K → ℝ)) (hwt_simplex : ∀ μ', wt μ' ∈ simplex K)
    (hwt_opt : ∀ μ' ∈ bestArmMeans F K, IsOptimalProportion F μ' (wt μ')) :
    (∀ ω : ℕ → Fin K × ℝ, FollowsDTracking wt ω → ∀ (t : ℕ) (a : Fin K),
      max (Real.sqrt (t : ℝ) - (K : ℝ) / 2) 0 - 1 ≤ (trajPullCount a t ω : ℝ)) ∧
    ∀ ε : ℝ, 0 < ε → ∀ t₀ : ℕ, ∃ tε : ℕ, t₀ ≤ tε ∧
      ∀ ω : ℕ → Fin K × ℝ, FollowsDTracking wt ω →
        ((∀ t : ℕ, t₀ ≤ t → ∀ a : Fin K, |wt (trajMeanVec t ω) a - w a| ≤ ε) →
          ∀ t : ℕ, tε ≤ t → ∀ a : Fin K,
            |(trajPullCount a t ω : ℝ) / (t : ℝ) - w a| ≤ 3 * ((K : ℝ) - 1) * ε) := by
  constructor
  · intro ω hω
    exact DTrackProof.forced_lower hK (fun t a => trajPullCount a t ω) (fun t => (ω t).1)
      (DTrackProof.count_step ω) (DTrackProof.forced_choice wt ω hω)
  · intro ε hε t₀
    exact DTrackProof.uniform_tracking hK w hw.1 wt hwt_simplex ε hε t₀


open Set Filter Topology
namespace OptimalBAI.TrackStop

lemma sorted_relabeling {K : ℕ} [NeZero K] (μ : Fin K → ℝ)
    (hK : 2 ≤ K) (best : Fin K) (hbest : IsBest μ best) :
    ∃ e : Equiv.Perm (Fin K), e 0=best ∧ μ (e 1)<μ (e 0) ∧
      ∀ a b : Fin K, 1 ≤ a → a ≤ b → μ (e b) ≤ μ (e a) := by
  let e := Tuple.sort (fun i => OrderDual.toDual (μ i))
  have hanti : Antitone (μ ∘ e) := Tuple.monotone_sort (fun i => OrderDual.toDual (μ i))
  have he0 : e 0=best := by
    by_contra hne
    have hlt := hbest (e 0) hne
    have hle := hanti (show (0 : Fin K) ≤ e.symm best from Fin.zero_le _)
    have hle' : μ best ≤ μ (e 0) := by
      simpa only [Function.comp_def,e.apply_symm_apply] using hle
    exact (not_le_of_gt hlt) hle'
  have h10 : (1 : Fin K) ≠ 0 := by
    intro h
    have he := congrArg Fin.val h
    rw [Fin.val_one',Fin.val_zero,Nat.mod_eq_of_lt (by omega : 1 < K)] at he
    omega
  refine ⟨e,he0,?_,fun a b _ hab => hanti hab⟩
  rw [he0]
  exact hbest (e 1) (fun h => h10 (e.injective (h.trans he0.symm)))

lemma optimal_unique {K : ℕ} (F : ExpFamily) (hK : 2 ≤ K)
    (μ : Fin K → ℝ) (hμ : μ ∈ bestArmMeans F K) (w v : Fin K → ℝ)
    (hw : IsOptimalProportion F μ w) (hv : IsOptimalProportion F μ v) : w=v := by
  letI : NeZero K := ⟨by omega⟩
  obtain ⟨best,hbest⟩ := hμ.2
  obtain ⟨e,he0,h10,hsorted⟩ := sorted_relabeling μ hK best hbest
  let G := F.toAllocationFamily
  have hm : ∀ a, (μ ∘ e) a ∈ G.M := fun a => hμ.1 (e a)
  obtain ⟨y,hy,hyF,_hunique,_hypos⟩ :=
    OptimalBAI.OptProportions.FFun_unique_level_one G (μ ∘ e) hK hm h10 hsorted
  have hw' := (bridge_optimal F (μ ∘ e) (w ∘ e)).mpr ((optimal_reindex e F μ w).mpr hw)
  have hv' := (bridge_optimal F (μ ∘ e) (v ∘ e)).mpr ((optimal_reindex e F μ v).mpr hv)
  have hwN := (OptimalBAI.OptProportions.optimal_iff_normalized G (μ ∘ e) hK hm h10 hsorted hy hyF (w ∘ e)).mp hw'
  have hvN := (OptimalBAI.OptProportions.optimal_iff_normalized G (μ ∘ e) hK hm h10 hsorted hy hyF (v ∘ e)).mp hv'
  funext i
  simpa using congrFun (hwN.trans hvN.symm) (e.symm i)

lemma optimal_weights_positive {K : ℕ} (F : ExpFamily) (hK : 2 ≤ K)
    (μ : Fin K → ℝ) (hμ : μ ∈ bestArmMeans F K) (w : Fin K → ℝ)
    (hw : IsOptimalProportion F μ w) : ∀ a, 0 < w a := by
  letI : NeZero K := ⟨by omega⟩
  obtain ⟨best,hbest⟩ := hμ.2
  let e := Equiv.swap (0 : Fin K) best
  have he0 : e 0=best := by simp [e]
  have hb : OptimalBAI.OptProportions.IsBest (μ ∘ e) 0 := by
    exact (isBest_reindex e μ 0).mpr (by simpa [he0] using hbest)
  have ho := (bridge_optimal F (μ ∘ e) (w ∘ e)).mpr ((optimal_reindex e F μ w).mpr hw)
  have hp := OptimalBAI.OptProportions.optimal_weights_pos F.toAllocationFamily (μ ∘ e)
    (w ∘ e) hK (fun a => hμ.1 (e a)) hb ho
  intro a
  simpa using hp (e.symm a)

end OptimalBAI.TrackStop


open Set Filter Topology
namespace OptimalBAI.TrackStop

lemma simplex_isCompact (K : ℕ) : IsCompact (simplex K) := by
  have hc : IsClosed (simplex K) := by
    have hpos : IsClosed {w : Fin K → ℝ | ∀ i, 0 ≤ w i} := by
      have hi : ∀ i : Fin K, IsClosed {w : Fin K → ℝ | (0 : ℝ) ≤ w i} :=
        fun i => isClosed_le continuous_const (continuous_apply i)
      convert isClosed_iInter hi using 1
      ext w
      simp
    exact hpos.inter
      (isClosed_eq (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const)
  apply (isCompact_Icc : IsCompact (Icc (fun _ : Fin K => (0 : ℝ)) (fun _ => (1 : ℝ)))).of_isClosed_subset hc
  intro w hw
  refine ⟨hw.1,fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)).trans_eq hw.2

lemma d_tendsto {ι : Type*} {l : Filter ι} (F : ExpFamily)
    {u v : ι → ℝ} {a b : ℝ} (ha : a ∈ F.M) (hb : b ∈ F.M)
    (hu : Tendsto u l (𝓝 a)) (hv : Tendsto v l (𝓝 b)) :
    Tendsto (fun i => F.d (u i) (v i)) l (𝓝 (F.d a b)) := by
  let G := F.toAllocationFamily
  have hθa := (G.parameter_continuousAt ha).tendsto.comp hu
  have hθb := (G.parameter_continuousAt hb).tendsto.comp hv
  have hba := (G.b_differentiableAt (G.parameter_mem ha)).continuousAt.tendsto.comp hθa
  have hbb := (G.b_differentiableAt (G.parameter_mem hb)).continuousAt.tendsto.comp hθb
  exact (hbb.sub hba).sub (hu.mul (hθb.sub hθa))

lemma pairCost_fixed_continuousAt (F : ExpFamily) {u v p q : ℝ}
    (hu : u ∈ F.M) (hv : v ∈ F.M) (hvu : v ≤ u)
    (hp : 0 < p) (hq : 0 < q) :
    ContinuousAt (fun x : ℝ × ℝ =>
      OptimalBAI.OptProportions.pairCost F.toAllocationFamily x.1 x.2 p q) (u,v) := by
  let G := F.toAllocationFamily
  have hd : p+q ≠ 0 := (add_pos hp hq).ne'
  have hm : OptimalBAI.OptProportions.pairMean u v p q ∈ F.M :=
    OptimalBAI.OptProportions.pairMean_mem G hu hv hvu hp.le hq.le
  have ht : Tendsto (fun x : ℝ × ℝ => OptimalBAI.OptProportions.pairMean x.1 x.2 p q)
      (𝓝 (u,v)) (𝓝 (OptimalBAI.OptProportions.pairMean u v p q)) := by
    simp only [OptimalBAI.OptProportions.pairMean,if_neg hd]
    exact ((continuous_fst.continuousAt.tendsto.const_mul p).add
      (continuous_snd.continuousAt.tendsto.const_mul q)).div_const _
  have h := (d_tendsto F hu hm continuous_fst.continuousAt.tendsto ht).const_mul p |>.add
    ((d_tendsto F hv hm continuous_snd.continuousAt.tendsto ht).const_mul q)
  change Tendsto (fun x : ℝ × ℝ => OptimalBAI.OptProportions.pairCost G x.1 x.2 p q)
    (𝓝 (u,v)) (𝓝 (OptimalBAI.OptProportions.pairCost G u v p q))
  simp_rw [OptimalBAI.OptProportions.pairCost_eq G hp.le hq.le]
  exact h

noncomputable def finiteCost {K : ℕ} [NeZero K] (hK : 2 ≤ K) (F : ExpFamily)
    (μ w : Fin K → ℝ) : ℝ :=
  (Finset.univ.erase (0 : Fin K)).inf' (OptimalBAI.OptProportions.other_arms_nonempty hK)
    (fun a => OptimalBAI.OptProportions.pairCost F.toAllocationFamily (μ 0) (μ a) (w 0) (w a))

lemma transportCost_eq_finiteCost {K : ℕ} [NeZero K] (hK : 2 ≤ K) (F : ExpFamily)
    (μ w : Fin K → ℝ) (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (hw : w ∈ simplex K) :
    transportCost F μ w = (finiteCost hK F μ w : EReal) := by
  obtain ⟨a,ha,hmin,he⟩ := OptimalBAI.OptProportions.transportCost_min_pair F.toAllocationFamily μ
    hK hμ hbest w hw
  have hf : finiteCost hK F μ w =
      OptimalBAI.OptProportions.pairCost F.toAllocationFamily (μ 0) (μ a) (w 0) (w a) := by
    unfold finiteCost
    exact le_antisymm (Finset.inf'_le _ (by simp [ha]))
      (Finset.le_inf' _ _ fun b hb => hmin b (Finset.mem_erase.mp hb).1)
  rw [hf]
  exact he

lemma finiteCost_continuousAt {K : ℕ} [NeZero K] (hK : 2 ≤ K) (F : ExpFamily)
    (μ w : Fin K → ℝ) (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (hw : ∀ a, 0 < w a) :
    ContinuousAt (fun m : Fin K → ℝ => finiteCost hK F m w) μ := by
  unfold finiteCost
  apply ContinuousAt.finset_inf'_apply
  intro a ha
  have hne : a ≠ 0 := (Finset.mem_erase.mp ha).1
  exact (pairCost_fixed_continuousAt F (hμ 0) (hμ a) (hbest a hne).le (hw 0) (hw a)).comp
    (f := fun m : Fin K → ℝ => (m 0,m a)) (x := μ)
    ((continuous_apply 0).prodMk (continuous_apply a)).continuousAt

end OptimalBAI.TrackStop


open Set Filter Topology
namespace OptimalBAI.TrackStop

lemma isBest_unique {K : ℕ} {μ : Fin K → ℝ} {a b : Fin K}
    (ha : IsBest μ a) (hb : IsBest μ b) : a=b := by
  by_contra hne
  have h1 := ha b (Ne.symm hne)
  have h2 := hb a hne
  linarith

lemma eventually_means_best_zero {K : ℕ} [NeZero K] {ι : Type*} {l : Filter ι}
    (F : ExpFamily) (μ : Fin K → ℝ) (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0)
    (m : ι → Fin K → ℝ) (hm : Tendsto m l (𝓝 μ)) :
    ∀ᶠ i in l, (∀ a, m i a ∈ F.M) ∧ IsBest (m i) 0 := by
  have hmem : ∀ᶠ i in l, ∀ a, m i a ∈ F.M := by
    apply eventually_all.mpr
    intro a
    exact ((continuous_apply a).continuousAt.tendsto.comp hm).eventually
      (F.toAllocationFamily.mean_isOpen.mem_nhds (hμ a))
  have hbest' : ∀ᶠ i in l, IsBest (m i) 0 := by
    apply eventually_all.mpr
    intro a
    by_cases ha : a=0
    · exact Filter.Eventually.of_forall (fun i hne => False.elim (hne ha))
    · have ho : IsOpen {m : Fin K → ℝ | m a < m 0} :=
        isOpen_lt (continuous_apply a) (continuous_apply 0)
      exact (hm.eventually (ho.mem_nhds (hbest a ha))).mono (fun i hi _ => hi)
  exact hmem.and hbest'

lemma optimal_selection_tendsto_zero {K : ℕ} [NeZero K] (F : ExpFamily) (hK : 2 ≤ K)
    (μ w : Fin K → ℝ) (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0)
    (hw : IsOptimalProportion F μ w) {ι : Type*} {l : Filter ι}
    (m v : ι → Fin K → ℝ) (hm : Tendsto m l (𝓝 μ))
    (hv : ∀ i, v i ∈ simplex K)
    (hopt : ∀ i, m i ∈ bestArmMeans F K → IsOptimalProportion F (m i) (v i)) :
    Tendsto v l (𝓝 w) := by
  apply (simplex_isCompact K).tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall hv)
  intro z hz hcl
  let L := Filter.comap v (𝓝 z) ⊓ l
  have hL : L.NeBot := by
    have hmap : (Filter.map v L).NeBot := by
      dsimp [L]
      rw [Filter.push_pull']
      exact hcl
    exact (Filter.map_neBot_iff v).mp hmap
  letI : L.NeBot := hL
  have hvL : Tendsto v L (𝓝 z) := tendsto_iff_comap.mpr inf_le_left
  have hmL : Tendsto m L (𝓝 μ) := hm.mono_left inf_le_right
  have hvalid := eventually_means_best_zero F μ hμ hbest m hmL
  have hwpos := optimal_weights_positive F hK μ ⟨hμ,0,hbest⟩ w hw
  have hcL := (finiteCost_continuousAt hK F μ w hμ hbest hwpos).tendsto.comp hmL
  have hcost : transportCost F μ w ≤ transportCost F μ z := by
    rw [transportCost_eq_finiteCost hK F μ w hμ hbest hw.1]
    unfold transportCost
    apply le_iInf
    intro lam
    apply le_iInf
    intro halt
    have hsum : Tendsto (fun i => ∑ a, v i a * F.d (m i a) (lam a)) L
        (𝓝 (∑ a, z a * F.d (μ a) (lam a))) := by
      apply tendsto_finset_sum
      intro a _
      exact ((continuous_apply a).continuousAt.tendsto.comp hvL).mul
        (d_tendsto F (hμ a) (halt.1.1 a)
          ((continuous_apply a).continuousAt.tendsto.comp hmL) tendsto_const_nhds)
    have hinequality : ∀ᶠ i in L, finiteCost hK F (m i) w ≤ ∑ a, v i a * F.d (m i a) (lam a) := by
      filter_upwards [hvalid] with i hi
      have hiopt := hopt i ⟨hi.1,0,hi.2⟩
      have hialt : lam ∈ Alt F (m i) := by
        refine ⟨halt.1,?_⟩
        intro a ha hia
        have he : a=0 := isBest_unique hia hi.2
        exact halt.2 a ha (by simpa [he] using hbest)
      have hcomp := (hiopt.2 w hw.1).trans (iInf_le_of_le lam (iInf_le_of_le hialt le_rfl))
      rw [transportCost_eq_finiteCost hK F (m i) w hi.1 hi.2 hw.1] at hcomp
      exact EReal.coe_le_coe_iff.mp hcomp
    exact EReal.coe_le_coe (le_of_tendsto_of_tendsto hcL hsum hinequality)
  have hzopt : IsOptimalProportion F μ z := ⟨hz,fun v' hv' => (hw.2 v' hv').trans hcost⟩
  exact optimal_unique F hK μ ⟨hμ,0,hbest⟩ z w hzopt hw

lemma optimal_selection_tendsto {K : ℕ} (F : ExpFamily) (hK : 2 ≤ K)
    (μ w : Fin K → ℝ) (hμ : μ ∈ bestArmMeans F K) (hw : IsOptimalProportion F μ w)
    {ι : Type*} {l : Filter ι} (m v : ι → Fin K → ℝ) (hm : Tendsto m l (𝓝 μ))
    (hv : ∀ i, v i ∈ simplex K)
    (hopt : ∀ i, m i ∈ bestArmMeans F K → IsOptimalProportion F (m i) (v i)) :
    Tendsto v l (𝓝 w) := by
  letI : NeZero K := ⟨by omega⟩
  obtain ⟨best,hbest⟩ := hμ.2
  let e := Equiv.swap (0 : Fin K) best
  have he0 : e 0=best := by simp [e]
  have hb : IsBest (μ ∘ e) 0 := (isBest_reindex e μ 0).mpr (by simpa [he0] using hbest)
  have hm' : Tendsto (fun i => m i ∘ e) l (𝓝 (μ ∘ e)) := by
    apply tendsto_pi_nhds.mpr
    intro a
    exact (continuous_apply (e a)).continuousAt.tendsto.comp hm
  have hv' := fun i => (simplex_reindex e (v i)).mpr (hv i)
  have hopt' : ∀ i, m i ∘ e ∈ bestArmMeans F K → IsOptimalProportion F (m i ∘ e) (v i ∘ e) := by
    intro i hi
    exact (optimal_reindex e F (m i) (v i)).mpr (hopt i ((bestMeans_reindex e (m i) F).mp hi))
  have hh := optimal_selection_tendsto_zero F hK (μ ∘ e) (w ∘ e) (fun a => hμ.1 (e a))
    hb ((optimal_reindex e F μ w).mpr hw) (fun i => m i ∘ e) (fun i => v i ∘ e) hm' hv' hopt'
  apply tendsto_pi_nhds.mpr
  intro a
  simpa only [Function.comp_def,e.apply_symm_apply] using
    (continuous_apply (e.symm a)).continuousAt.tendsto.comp hh

end OptimalBAI.TrackStop


open BanditAlgorithm Filter Topology
set_option maxHeartbeats 1500000
namespace OptimalBAI.TrackStop

lemma c_tracking_limit {K : ℕ} (wt : (Fin K → ℝ) → (Fin K → ℝ))
    (hwt : ∀ μ', wt μ' ∈ simplex K) (w : Fin K → ℝ)
    (ω : ℕ → Fin K × ℝ) (hω : FollowsCTracking wt ω)
    (hv : Tendsto (fun n => wt (trajMeanVec n ω)) atTop (𝓝 w)) :
    ∀ a, Tendsto (fun n => (trajPullCount a n ω : ℝ)/(n : ℝ)) atTop (𝓝 (w a)) := by
  intro a
  have hu := (continuous_apply a).continuousAt.tendsto.comp hv
  have hav : Tendsto (fun n => (∑ s ∈ Finset.range n,wt (trajMeanVec s ω) a)/(n : ℝ))
      atTop (𝓝 (w a)) := by
    simpa only [div_eq_mul_inv,mul_comm,Function.comp_apply] using hu.cesaro
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hb : Tendsto (fun n : ℕ => (K : ℝ)*(1+Real.sqrt n)/(n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_div_assoc,add_div,one_div,Real.sqrt_div_self,mul_zero,add_zero] using
      tendsto_const_nhds.mul (hi.add hs)
  have he : Tendsto (fun n => (trajPullCount a n ω : ℝ)/(n : ℝ)-
      (∑ s ∈ Finset.range n,wt (trajMeanVec s ω) a)/(n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero_norm' _ hb
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have h := (c_tracking_bounds_reused wt hwt ω hω n hn a).2
    rw [Real.norm_eq_abs,← sub_div,abs_div,abs_of_nonneg (a := (n : ℝ)) (Nat.cast_nonneg n)]
    exact div_le_div_of_nonneg_right h (Nat.cast_nonneg n)
  simpa only [sub_add_cancel,zero_add] using he.add hav

lemma d_tracking_limit (F : ExpFamily) {K : ℕ} (hK : 2 ≤ K)
    (μ : Fin K → ℝ) (hμ : μ ∈ bestArmMeans F K) (w : Fin K → ℝ)
    (hw : IsOptimalProportion F μ w) (wt : (Fin K → ℝ) → (Fin K → ℝ))
    (hwt : ∀ μ', wt μ' ∈ simplex K)
    (hwtopt : ∀ μ' ∈ bestArmMeans F K, IsOptimalProportion F μ' (wt μ'))
    (ω : ℕ → Fin K × ℝ) (hω : FollowsDTracking wt ω)
    (hv : Tendsto (fun n => wt (trajMeanVec n ω)) atTop (𝓝 w)) :
    ∀ a, Tendsto (fun n => (trajPullCount a n ω : ℝ)/(n : ℝ)) atTop (𝓝 (w a)) := by
  have hKr : (2 : ℝ)≤K := by exact_mod_cast hK
  have hkmpos : 0<(K : ℝ)-1 := by linarith
  intro a
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε/(6*((K : ℝ)-1))
  have hη : 0<η := by dsimp [η]; positivity
  have hh : ∀ᶠ n : ℕ in atTop, ∀ b, |wt (trajMeanVec n ω) b-w b| ≤ η := by
    apply eventually_all.mpr
    intro b
    have hb := ((continuous_apply b).continuousAt.tendsto.comp hv).eventually
      (Metric.closedBall_mem_nhds _ hη)
    simpa only [Metric.mem_closedBall,Real.dist_eq,Function.comp_apply] using hb
  obtain ⟨t₀,ht₀⟩ := eventually_atTop.mp hh
  obtain ⟨tε,htε,hbound⟩ :=
    (d_tracking_bounds_reused F hK μ hμ w hw wt hwt hwtopt).2 η hη t₀
  filter_upwards [eventually_ge_atTop tε] with n hn
  have h := hbound ω hω ht₀ n hn a
  have hcalc : 3*((K : ℝ)-1)*η=ε/2 := by
    dsimp [η]
    field_simp [hkmpos.ne']
    ring
  rw [hcalc] at h
  simpa only [Real.dist_eq] using h.trans_lt (by linarith : ε/2<ε)

end OptimalBAI.TrackStop


open MeasureTheory ProbabilityTheory BanditAlgorithm Filter Topology
set_option maxHeartbeats 1500000
namespace OptimalBAI.TrackStop

lemma tracking_forced (F : ExpFamily) {K : ℕ} (hK : 2≤K)
    (θ : Fin K → F.Θ) (hθ : θ ∈ Sθ F K)
    (w : Fin K → ℝ) (hw : IsOptimalProportion F (meanVec F θ) w)
    (wt : (Fin K → ℝ) → (Fin K → ℝ)) (hwt : ∀ μ', wt μ' ∈ simplex K)
    (hwtopt : ∀ μ' ∈ bestArmMeans F K, IsOptimalProportion F μ' (wt μ'))
    (π : BanditPolicy K) (hπ : IsCTrackingPolicy wt π ∨ IsDTrackingPolicy wt π) :
    ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F θ) π, ∀ᶠ n : ℕ in atTop,
      ∀ a, Real.sqrt n-2*(K : ℝ)≤(trajPullCount a n ω : ℝ) := by
  have hμ : meanVec F θ ∈ bestArmMeans F K :=
    ⟨fun a => ⟨θ a,(θ a).2,rfl⟩,hθ⟩
  rcases hπ with hC | hD
  · filter_upwards [policy_follows_C (expFamilyBandit F θ) π wt hC] with ω hω
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    intro a
    have hh := (c_tracking_bounds_reused wt hwt ω hω n hn a).1
    have hs : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ)+(K : ℝ)^2) :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (K : ℝ)])
    linarith
  · filter_upwards [policy_follows_D (expFamilyBandit F θ) π wt hD] with ω hω
    exact Eventually.of_forall (fun n a => by
      have hh := (d_tracking_bounds_reused F hK (meanVec F θ) hμ w hw wt hwt hwtopt).1 ω hω n a
      have hx := le_max_left (Real.sqrt (n : ℝ)-(K : ℝ)/2) 0
      have hKr : (2 : ℝ)≤K := by exact_mod_cast hK
      linarith)

lemma tracking_converges (F : ExpFamily) {K : ℕ} (hK : 2 ≤ K)
    (θ : Fin K → F.Θ) (hθ : θ ∈ Sθ F K)
    (w : Fin K → ℝ) (hw : IsOptimalProportion F (meanVec F θ) w)
    (wt : (Fin K → ℝ) → (Fin K → ℝ)) (hwt_simplex : ∀ μ', wt μ' ∈ simplex K)
    (hwt_opt : ∀ μ' ∈ bestArmMeans F K, IsOptimalProportion F μ' (wt μ'))
    (π : BanditPolicy K) (hπ : IsCTrackingPolicy wt π ∨ IsDTrackingPolicy wt π) :
    ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F θ) π, ∀ a : Fin K,
      Tendsto (fun t : ℕ => (trajPullCount a t ω : ℝ)/(t : ℝ)) atTop (𝓝 (w a)) := by
  have hμ : meanVec F θ ∈ bestArmMeans F K :=
    ⟨fun a => ⟨θ a,(θ a).2,rfl⟩,hθ⟩
  have hmeans := empirical_consistency_forced F θ π (2*(K : ℝ))
    (tracking_forced F hK θ hθ w hw wt hwt_simplex hwt_opt π hπ)
  rcases hπ with hC | hD
  · filter_upwards [hmeans,policy_follows_C (expFamilyBandit F θ) π wt hC] with ω hmean hω
    apply c_tracking_limit wt hwt_simplex w ω hω
    exact optimal_selection_tendsto F hK (meanVec F θ) w hμ hw
      (fun t => trajMeanVec t ω) (fun t => wt (trajMeanVec t ω)) hmean
      (fun t => hwt_simplex _) (fun t ht => hwt_opt _ ht)
  · filter_upwards [hmeans,policy_follows_D (expFamilyBandit F θ) π wt hD] with ω hmean hω
    apply d_tracking_limit F hK (meanVec F θ) hμ w hw wt hwt_simplex hwt_opt ω hω
    exact optimal_selection_tendsto F hK (meanVec F θ) w hμ hw
      (fun t => trajMeanVec t ω) (fun t => wt (trajMeanVec t ω)) hmean
      (fun t => hwt_simplex _) (fun t ht => hwt_opt _ ht)

end OptimalBAI.TrackStop


open MeasureTheory BanditAlgorithm Filter Topology
open scoped ENNReal
set_option maxHeartbeats 1500000
namespace OptimalBAI.TrackStop

lemma tracking_forced_all (F : ExpFamily) {K : ℕ} (hK : 2≤K)
    (θ : Fin K → F.Θ) (hθ : θ∈Sθ F K) (w : Fin K → ℝ)
    (hw : IsOptimalProportion F (meanVec F θ) w)
    (wt : (Fin K → ℝ) → Fin K → ℝ) (hwt : ∀ μ, wt μ∈simplex K)
    (hwtopt : ∀ μ∈bestArmMeans F K, IsOptimalProportion F μ (wt μ))
    (π : BanditPolicy K) (hπ : IsCTrackingPolicy wt π ∨ IsDTrackingPolicy wt π) :
    ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F θ) π, ∀ n : ℕ, 1≤n →
      ∀ a, Real.sqrt n-2*(K : ℝ)≤(trajPullCount a n ω : ℝ) := by
  have hμ : meanVec F θ∈bestArmMeans F K := ⟨fun a => ⟨θ a,(θ a).2,rfl⟩,hθ⟩
  rcases hπ with hC | hD
  · filter_upwards [policy_follows_C (expFamilyBandit F θ) π wt hC] with ω hω
    intro n hn a
    have hh := (c_tracking_bounds_reused wt hwt ω hω n hn a).1
    have hs : Real.sqrt (n : ℝ)≤Real.sqrt ((n : ℝ)+(K : ℝ)^2) :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (K : ℝ)])
    linarith
  · filter_upwards [policy_follows_D (expFamilyBandit F θ) π wt hD] with ω hω
    intro n hn a
    have hh := (d_tracking_bounds_reused F hK (meanVec F θ) hμ w hw wt hwt hwtopt).1 ω hω n a
    have hx := le_max_left (Real.sqrt (n : ℝ)-(K : ℝ)/2) 0
    have hKr : (2 : ℝ)≤K := by exact_mod_cast hK
    linarith

lemma integrable_settling (F : ExpFamily) {K : ℕ} (hK : 2≤K)
    (θ : Fin K → F.Θ) (hθ : θ∈Sθ F K) (w : Fin K → ℝ)
    (hw : IsOptimalProportion F (meanVec F θ) w)
    (wt : (Fin K → ℝ) → Fin K → ℝ) (hwt : ∀ μ, wt μ∈simplex K)
    (hwtopt : ∀ μ∈bestArmMeans F K, IsOptimalProportion F μ (wt μ))
    (π : BanditPolicy K) (hπ : IsCTrackingPolicy wt π ∨ IsDTrackingPolicy wt π)
    (ε : ℝ) (hε : 0<ε) :
    ∃ t₀ : (ℕ → Fin K × ℝ) → ℕ, Measurable t₀ ∧
      (∫⁻ ω, (t₀ ω : ℝ≥0∞) ∂banditTrajMeasure (expFamilyBandit F θ) π)≠⊤ ∧
      ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F θ) π, ∀ n : ℕ, t₀ ω≤n →
        ∀ a, |trajMeanVec n ω a-meanVec F θ a|≤ε := by
  let P := banditTrajMeasure (expFamilyBandit F θ) π
  let Y := badDelay F θ (2*(K : ℝ)) ε
  have hYm : Measurable Y := badDelay_measurable F θ _ _
  have hYi : (∫⁻ ω,Y ω ∂P)≠⊤ := badDelay_integral_finite F θ π _ ε hε
  have hYa : ∀ᵐ ω ∂P,Y ω<⊤ := ae_lt_top hYm hYi
  have hlarge : ∀ᶠ n : ℕ in atTop, 1≤n ∧ 0<Real.sqrt n-2*(K : ℝ) := by
    have hh := (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop (2*(K : ℝ))
    filter_upwards [hh,eventually_ge_atTop (1 : ℕ)] with n hn hn1
    simp only [Function.comp_apply] at hn
    exact ⟨hn1,by linarith⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hlarge
  let t₀ := fun ω => Nat.ceil (Y ω).toReal+N+1
  have ht₀m : Measurable t₀ := by
    exact ((hYm.ennreal_toReal).nat_ceil.add_const N).add_const 1
  refine ⟨t₀,ht₀m,?_,?_⟩
  · have hb : ∀ᵐ ω ∂P, (t₀ ω : ℝ≥0∞)≤Y ω+(N+2 : ℝ≥0∞) := by
      filter_upwards [hYa] with ω hω
      have hc := Nat.ceil_lt_add_one (ENNReal.toReal_nonneg : 0≤(Y ω).toReal)
      have hh : (t₀ ω : ℝ)≤(Y ω).toReal+(N+2 : ℝ) := by
        simp only [t₀,Nat.cast_add,Nat.cast_one]
        linarith
      have hh' := ENNReal.ofReal_le_ofReal hh
      simpa only [ENNReal.ofReal_natCast,ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity : 0≤(N+2 : ℝ)),
        ENNReal.ofReal_toReal hω.ne,ENNReal.ofReal_add (Nat.cast_nonneg N) (by norm_num : (0 : ℝ)≤2),
        ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat] using hh'
    apply ne_top_of_le_ne_top _ (lintegral_mono_ae hb)
    rw [lintegral_add_left hYm,lintegral_const]
    simp [hYi]
  · filter_upwards [hYa,tracking_forced_all F hK θ hθ w hw wt hwt hwtopt π hπ] with ω hY hforced
    intro n hn a
    have hnN : N≤n := by dsimp [t₀] at hn; omega
    have hcn := hforced n (hN n hnN).1 a
    have hp : 0<trajPullCount a n ω := by exact_mod_cast ((hN n hnN).2.trans_le hcn)
    by_contra hbad
    have he : ω∈badEstimate F θ (2*(K : ℝ)) ε n a := ⟨hp,hcn,(lt_of_not_ge hbad).le⟩
    have hh := badDelay_dominates F θ (2*(K : ℝ)) ε ω n a he
    have hhR : (n : ℝ)+1≤(Y ω).toReal := by
      have hh' := (ENNReal.toReal_le_toReal (by simp : (n+1 : ℝ≥0∞)≠⊤) hY.ne).mpr hh
      simpa only [ENNReal.toReal_add (by simp : (n : ℝ≥0∞)≠⊤) ENNReal.one_ne_top,ENNReal.toReal_natCast,ENNReal.toReal_one] using hh'
    have hc : (Y ω).toReal≤(Nat.ceil (Y ω).toReal : ℝ) := Nat.le_ceil _
    have hnn : (Nat.ceil (Y ω).toReal : ℝ)+1≤(n : ℝ) := by
      have hn' : Nat.ceil (Y ω).toReal+1≤n := by dsimp [t₀] at hn; omega
      exact_mod_cast hn'
    linarith

end OptimalBAI.TrackStop


open Filter Topology
set_option maxHeartbeats 1500000
namespace OptimalBAI.TrackStop

lemma pairCost_scaling (F : ExpFamily) (u v p q c : ℝ) (hc : c≠0) (hpq : p+q≠0) :
    OptProportions.pairCost F.toAllocationFamily u v (c*p) (c*q)=
      c*OptProportions.pairCost F.toAllocationFamily u v p q := by
  unfold OptProportions.pairCost
  have hr : c*p/(c*p+c*q)=p/(p+q) := by
    rw [← mul_add]
    exact mul_div_mul_left _ _ hc
  rw [hr]
  ring

lemma pairCost_tendsto (F : ExpFamily) {ι : Type*} {l : Filter ι}
    {u v p q : ι → ℝ} {U V P Q : ℝ}
    (hU : U∈F.M) (hV : V∈F.M) (hVU : V≤U) (hP : 0<P) (hQ : 0<Q)
    (hu : Tendsto u l (𝓝 U)) (hv : Tendsto v l (𝓝 V))
    (hp : Tendsto p l (𝓝 P)) (hq : Tendsto q l (𝓝 Q)) :
    Tendsto (fun i => OptProportions.pairCost F.toAllocationFamily (u i) (v i) (p i) (q i))
      l (𝓝 (OptProportions.pairCost F.toAllocationFamily U V P Q)) := by
  let G := F.toAllocationFamily
  have hPQ : P+Q≠0 := (add_pos hP hQ).ne'
  have hpos : ∀ᶠ i in l, 0≤p i ∧ 0≤q i ∧ p i+q i≠0 := by
    filter_upwards [hp.eventually (eventually_gt_nhds hP),hq.eventually (eventually_gt_nhds hQ)] with i hi hj
    exact ⟨hi.le,hj.le,(add_pos hi hj).ne'⟩
  let m := fun i => OptProportions.pairMean (u i) (v i) (p i) (q i)
  have hm : Tendsto m l (𝓝 (OptProportions.pairMean U V P Q)) := by
    have h := ((hp.mul hu).add (hq.mul hv)).div (hp.add hq) hPQ
    have he : m =ᶠ[l] fun i => (p i*u i+q i*v i)/(p i+q i) := by
      filter_upwards [hpos] with i hi
      simp only [m,OptProportions.pairMean,if_neg hi.2.2]
    rw [OptProportions.pairMean,if_neg hPQ]
    exact h.congr' he.symm
  have hM : OptProportions.pairMean U V P Q ∈ F.M :=
    OptProportions.pairMean_mem G hU hV hVU hP.le hQ.le
  have h := (hp.mul (d_tendsto F hU hM hu hm)).add (hq.mul (d_tendsto F hV hM hv hm))
  rw [OptProportions.pairCost_eq G hP.le hQ.le]
  apply h.congr'
  filter_upwards [hpos] with i hi
  exact (OptProportions.pairCost_eq G hi.1 hi.2.1).symm

end OptimalBAI.TrackStop


open Filter Topology
set_option maxHeartbeats 1500000
namespace OptimalBAI.TrackStop

lemma local_information (F : ExpFamily) {K : ℕ} (μ w : Fin K → ℝ)
    (hμ : ∀ a, μ a∈F.M) (hw : ∀ a, 0<w a) (best : Fin K) (hbest : IsBest μ best)
    (I : ℝ) (hpair : ∀ b, b≠best → I≤OptProportions.pairCost F.toAllocationFamily (μ best) (μ b) (w best) (w b))
    (c : ℝ) (hc : c<I) :
    ∃ η : ℝ, 0<η ∧ ∀ m p : Fin K → ℝ,
      (∀ a, |m a-μ a|≤η) → (∀ a, |p a-w a|≤η) →
      (∀ a, m a∈F.M ∧ 0<p a) ∧ IsBest m best ∧
        ∀ b, b≠best → c<OptProportions.pairCost F.toAllocationFamily (m best) (m b) (p best) (p b) := by
  let X := (Fin K → ℝ) × (Fin K → ℝ)
  have htm (a : Fin K) : Tendsto (fun x : X => x.1 a) (𝓝 (μ,w)) (𝓝 (μ a)) :=
    ((continuous_apply a).comp continuous_fst).continuousAt.tendsto
  have htp (a : Fin K) : Tendsto (fun x : X => x.2 a) (𝓝 (μ,w)) (𝓝 (w a)) :=
    ((continuous_apply a).comp continuous_snd).continuousAt.tendsto
  have hcoords : ∀ᶠ x : X in 𝓝 (μ,w), ∀ a, x.1 a∈F.M ∧ 0<x.2 a := by
    apply eventually_all.mpr
    intro a
    have hm := (htm a).eventually
      (F.toAllocationFamily.mean_isOpen.mem_nhds (hμ a))
    have hp := (htp a).eventually
      (eventually_gt_nhds (hw a))
    exact hm.and hp
  have hbest' : ∀ᶠ x : X in 𝓝 (μ,w), IsBest x.1 best := by
    apply eventually_all.mpr
    intro b
    by_cases hb : b=best
    · exact Eventually.of_forall (fun _ h => (h hb).elim)
    have hi := (htm b).eventually_lt (htm best) (hbest b hb)
    exact hi.mono (fun _ h _ => h)
  have hpairs : ∀ᶠ x : X in 𝓝 (μ,w), ∀ b, b≠best →
      c<OptProportions.pairCost F.toAllocationFamily (x.1 best) (x.1 b) (x.2 best) (x.2 b) := by
    apply eventually_all.mpr
    intro b
    by_cases hb : b=best
    · exact Eventually.of_forall (fun _ h => (h hb).elim)
    have ht := pairCost_tendsto F (hμ best) (hμ b) (hbest b hb).le (hw best) (hw b)
      (htm best) (htm b) (htp best) (htp b)
    exact (ht.eventually (eventually_gt_nhds (hc.trans_le (hpair b hb)))).mono (fun _ h _ => h)
  obtain ⟨ρ,hρ,hgood⟩ := Metric.eventually_nhds_iff.mp (hcoords.and (hbest'.and hpairs))
  refine ⟨ρ/2,by positivity,?_⟩
  intro m p hm hp
  have hmD : dist m μ≤ρ/2 := (dist_pi_le_iff (by positivity)).mpr (by simpa only [Real.dist_eq] using hm)
  have hpD : dist p w≤ρ/2 := (dist_pi_le_iff (by positivity)).mpr (by simpa only [Real.dist_eq] using hp)
  apply hgood (y := (m,p))
  rw [Prod.dist_eq]
  exact (max_le hmD hpD).trans_lt (by linarith)

lemma target_local (F : ExpFamily) {K : ℕ} (hK : 2≤K)
    (μ w : Fin K → ℝ) (hμ : μ∈bestArmMeans F K) (hw : IsOptimalProportion F μ w)
    (wt : (Fin K → ℝ) → Fin K → ℝ) (hwt : ∀ m, wt m∈simplex K)
    (hwtopt : ∀ m∈bestArmMeans F K, IsOptimalProportion F m (wt m))
    (η : ℝ) (hη : 0<η) :
    ∃ ρ : ℝ, 0<ρ ∧ ∀ m : Fin K → ℝ,
      (∀ a, |m a-μ a|≤ρ) → ∀ a, |wt m a-w a|≤η := by
  have ht : Tendsto wt (𝓝 μ) (𝓝 w) := optimal_selection_tendsto F hK μ w hμ hw id wt continuous_id.continuousAt.tendsto hwt
    (fun m hm => hwtopt m hm)
  have he : ∀ᶠ m in 𝓝 μ, ∀ a, |wt m a-w a|≤η := by
    apply eventually_all.mpr
    intro a
    have ha := ((continuous_apply a).continuousAt.tendsto.comp ht).eventually
      (Metric.closedBall_mem_nhds _ hη)
    simpa only [Metric.mem_closedBall,Real.dist_eq,Function.comp_apply] using ha
  obtain ⟨r,hr,hgood⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r/2,by positivity,?_⟩
  intro m hm
  have hd : dist m μ≤r/2 := (dist_pi_le_iff (by positivity)).mpr (by simpa only [Real.dist_eq] using hm)
  exact hgood (y := m) (hd.trans_lt (by linarith))

end OptimalBAI.TrackStop


open BanditAlgorithm Filter Topology
set_option maxHeartbeats 1500000
namespace OptimalBAI.TrackStop

lemma simplex_coordinate_le_one {K : ℕ} {w : Fin K → ℝ} (hw : w∈simplex K) (a : Fin K) : w a≤1 := by
  calc
    w a≤∑ b,w b := Finset.single_le_sum (fun b _ => hw.1 b) (Finset.mem_univ a)
    _=1 := hw.2

lemma sum_target_error {K : ℕ} (v : ℕ → Fin K → ℝ) (w : Fin K → ℝ)
    (hv : ∀ n, v n∈simplex K) (hw : w∈simplex K)
    (ε : ℝ) (hε : 0≤ε) (t₀ : ℕ)
    (hclose : ∀ n, t₀≤n → ∀ a, |v n a-w a|≤ε) (t : ℕ) (ht : t₀≤t) (a : Fin K) :
    |(∑ s∈Finset.range t,v s a)-(t : ℝ)*w a|≤(t₀ : ℝ)+(t : ℝ)*ε := by
  have hsum : (∑ s∈Finset.range t,(v s a-w a))=
      (∑ s∈Finset.range t₀,(v s a-w a))+
      ∑ s∈Finset.range (t-t₀),(v (t₀+s) a-w a) := by
    simpa only [Nat.add_sub_of_le ht] using Finset.sum_range_add (fun s => v s a-w a) t₀ (t-t₀)
  have hleft : |∑ s∈Finset.range t₀,(v s a-w a)|≤(t₀ : ℝ) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _≤∑ s∈Finset.range t₀,(1 : ℝ) := by
        apply Finset.sum_le_sum
        intro s hs
        exact abs_le.mpr ⟨by linarith [(hv s).1 a,simplex_coordinate_le_one hw a],
          by linarith [hw.1 a,simplex_coordinate_le_one (hv s) a]⟩
      _=(t₀ : ℝ) := by simp
  have hright : |∑ s∈Finset.range (t-t₀),(v (t₀+s) a-w a)|≤(t-t₀ : ℕ)*ε := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _≤∑ s∈Finset.range (t-t₀),ε := by
        exact Finset.sum_le_sum (fun s _ => hclose (t₀+s) (Nat.le_add_right _ _) a)
      _= _ := by simp
  have heq : (∑ s∈Finset.range t,(v s a-w a))=(∑ s∈Finset.range t,v s a)-(t : ℝ)*w a := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [←heq,hsum]
  apply (abs_add_le _ _).trans
  have hcast : (t-t₀ : ℕ)≤t := Nat.sub_le _ _
  have hh : ((t-t₀ : ℕ) : ℝ)*ε≤(t : ℝ)*ε := mul_le_mul_of_nonneg_right (by exact_mod_cast hcast) hε
  linarith

lemma c_tracking_linear {K : ℕ} (wt : (Fin K → ℝ) → Fin K → ℝ)
    (hwt : ∀ μ',wt μ'∈simplex K) (w : Fin K → ℝ) (hw : w∈simplex K)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C B : ℝ, 0<C ∧ 0≤B ∧ ∀ t₀ : ℕ, ∀ ω : ℕ → Fin K × ℝ,
      FollowsCTracking wt ω →
      (∀ n : ℕ, t₀≤n → ∀ a, |wt (trajMeanVec n ω) a-w a|≤ε) →
      ∀ t : ℕ, C*(t₀ : ℝ)+B≤(t : ℝ) → ∀ a,
        |(trajPullCount a t ω : ℝ)/(t : ℝ)-w a|≤3*ε := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hb : Tendsto (fun n : ℕ => (K : ℝ)*(1+Real.sqrt n)/(n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_div_assoc,add_div,one_div,Real.sqrt_div_self,mul_zero,add_zero] using
      tendsto_const_nhds.mul (hi.add hs)
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hb.eventually (eventually_le_nhds hε))
  let L := 1+1/ε
  let T' := max 1 T
  have hL : 1≤L := by dsimp [L]; linarith [one_div_pos.mpr hε]
  have hLp : 0<L := lt_of_lt_of_le zero_lt_one hL
  refine ⟨L,L*(T' : ℝ),hLp,by positivity,?_⟩
  intro t₀ ω hω hclose t ht a
  have htt₀ : t₀≤t := by
    have hh := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg (α := ℝ) t₀)
    have hh' : (t₀ : ℝ)≤(t : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) T']
    exact_mod_cast hh'
  have htT' : T'≤t := by
    have hh := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg (α := ℝ) T')
    have hh' : (T' : ℝ)≤(t : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) t₀]
    exact_mod_cast hh'
  have ht1 : 1≤t := (le_max_left 1 T).trans htT'
  have htp : (0 : ℝ)<t := by exact_mod_cast ht1
  have htε : (t₀ : ℝ)≤ε*(t : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left ht hε.le
    have hident : ε*L=ε+1 := by dsimp [L]; field_simp [hε.ne']
    have hid : ε*(L*(t₀ : ℝ)+L*(T' : ℝ))=(ε+1)*((t₀ : ℝ)+(T' : ℝ)) := by rw [←mul_add,←mul_assoc,hident]
    rw [hid] at hh
    nlinarith [Nat.cast_nonneg (α := ℝ) T',Nat.cast_nonneg (α := ℝ) t₀]
  have htrack := (c_tracking_bounds_reused wt hwt ω hω t ht1 a).2
  have hsum := sum_target_error (fun n => wt (trajMeanVec n ω)) w (fun n => hwt _) hw ε hε.le t₀ hclose t htt₀ a
  have herr := (div_le_iff₀ htp).mp (hT t ((le_max_right 1 T).trans htT'))
  have hh : |(trajPullCount a t ω : ℝ)-(t : ℝ)*w a|≤3*ε*(t : ℝ) := by
    have he : (trajPullCount a t ω : ℝ)-(t : ℝ)*w a=
        ((trajPullCount a t ω : ℝ)-(∑ s∈Finset.range t,wt (trajMeanVec s ω) a))+
        ((∑ s∈Finset.range t,wt (trajMeanVec s ω) a)-(t : ℝ)*w a) := by ring
    rw [he]
    exact (abs_add_le _ _).trans (by linarith)
  have he : (trajPullCount a t ω : ℝ)/(t : ℝ)-w a=
      ((trajPullCount a t ω : ℝ)-(t : ℝ)*w a)/(t : ℝ) := by field_simp
  rw [he,abs_div,abs_of_pos htp]
  exact (div_le_iff₀ htp).mpr hh

end OptimalBAI.TrackStop

/- Reused from accepted submission fc848517-a37c-4820-ab51-0a5501c47bf8. -/
open scoped BigOperators
open BanditAlgorithm OptimalBAI.TrackStop
namespace DUniformProof
private theorem forced_lower {K : ℕ} (hK : 2 ≤ K) (N : ℕ → Fin K → ℕ) (I : ℕ → Fin K)
    (hstep : ∀ t a, N (t+1) a = N t a + if a = I t then 1 else 0)
    (hsel : ∀ (t : ℕ) a, (N t a : ℝ) < Real.sqrt (t : ℝ) - (K : ℝ)/2 → N t (I t) ≤ N t a) :
    ∀ (t : ℕ) a, max (Real.sqrt (t : ℝ)-(K : ℝ)/2) 0 - 1 ≤ (N t a : ℝ) := by
  classical
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hmono : ∀ a, Monotone (fun t => N t a) := fun a => monotone_nat_of_le_succ fun t => by
    rw [hstep]; omega
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro a
    by_contra! hbad
    let q := N t a
    have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
    have hbad' : (q : ℝ)+1 < Real.sqrt (t : ℝ)-(K : ℝ)/2 := by
      have hmax := (lt_max_iff.mp (show (q : ℝ)+1 < max (Real.sqrt (t : ℝ)-(K : ℝ)/2) 0 by linarith))
      rcases hmax with ht | ht
      · exact ht
      · linarith
    have hsqt := Real.sq_sqrt (Nat.cast_nonneg t)
    have htK : K ≤ t := by
      have : (K : ℝ) < t := by nlinarith [sq_nonneg ((K : ℝ)/2)]
      exact_mod_cast this.le
    let u := t-K
    have hu : u < t := by dsimp [u]; omega
    have hu_cast : (u : ℝ) = (t : ℝ)-(K : ℝ) := by dsimp [u]; exact Nat.cast_sub htK
    have hsqu := Real.sq_sqrt (Nat.cast_nonneg u)
    have hsqrt : Real.sqrt (t : ℝ)-1 < Real.sqrt (u : ℝ) := by
      apply (sq_lt_sq₀ (by linarith : 0 ≤ Real.sqrt (t : ℝ)-1) (Real.sqrt_nonneg _)).mp
      rw [hsqu, hu_cast]
      nlinarith
    have huq : (q : ℝ) < Real.sqrt (u : ℝ)-(K : ℝ)/2 := by linarith
    have hbase : ∀ b, q ≤ N u b := by
      intro b
      have hh := ih u hu b
      have hm := le_max_left (Real.sqrt (u : ℝ)-(K : ℝ)/2) 0
      have hc : (q : ℝ) < (N u b : ℝ)+1 := by linarith
      have hc' : q < N u b+1 := by exact_mod_cast hc
      omega
    have hchoose : ∀ j, u ≤ j → j < t → N j (I j) = q := by
      intro j hj hjt
      have hja : N j a ≤ q := hmono a hjt.le
      have ht : (N j a : ℝ) < Real.sqrt (j : ℝ)-(K : ℝ)/2 := by
        have hsj := Real.sqrt_le_sqrt (show (u : ℝ) ≤ j by exact_mod_cast hj)
        have hjr : (N j a : ℝ) ≤ q := by exact_mod_cast hja
        linarith
      exact le_antisymm ((hsel j a ht).trans hja) ((hbase (I j)).trans (hmono (I j) hj))
    let S : ℕ → ℕ := fun j => ∑ b, min (N j b) (q+1)
    have hSstep : ∀ j, u ≤ j → j < t → S (j+1) = S j+1 := by
      intro j hj hjt
      have he : ∀ b, min (N (j+1) b) (q+1) = min (N j b) (q+1) + if b = I j then 1 else 0 := by
        intro b
        rw [hstep]
        by_cases hb : b = I j
        · subst b; rw [hchoose j hj hjt]; simp
        · simp [hb]
      dsimp only [S]
      simp_rw [he]
      rw [Finset.sum_add_distrib]
      simp
    have hSeq : ∀ j, u ≤ j → j ≤ t → S j = S u+(j-u) := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => simp
      | succ j hj ih =>
        intro hjt
        rw [hSstep j hj (by omega), ih (by omega)]
        omega
    have hSlower : K*q ≤ S u := by
      calc K*q = ∑ _b : Fin K, q := by simp
           _ ≤ S u := Finset.sum_le_sum (fun b _ => le_min (hbase b) (by omega))
    have hSupper : S t < K*(q+1) := by
      calc S t < ∑ _b : Fin K, (q+1) := by
             dsimp only [S]
             apply Finset.sum_lt_sum (fun b _ => min_le_right _ _)
             refine ⟨a, Finset.mem_univ a, ?_⟩
             dsimp only [q]; omega
           _ = K*(q+1) := by simp
    have htS := hSeq t (by dsimp [u]; omega) le_rfl
    have htu : t-u = K := by dsimp [u]; omega
    rw [htu] at htS
    nlinarith
private theorem sqrt_small (ε : ℝ) (hε : 0 < ε) (T : ℕ) (hT : 1/ε^2 ≤ (T : ℝ))
    (t : ℕ) (ht : T ≤ t) : Real.sqrt (t : ℝ) ≤ ε*(t : ℝ) := by
  have he : ε^2 ≠ 0 := pow_ne_zero _ hε.ne'
  have hmul : 1 ≤ ε^2*(t : ℝ) := by
    have hh : 1/ε^2 ≤ (t : ℝ) := hT.trans (by exact_mod_cast ht)
    exact (div_le_iff₀ (sq_pos_of_pos hε)).mp hh |>.trans_eq (mul_comm _ _)
  have hs := Real.sq_sqrt (Nat.cast_nonneg t)
  have heq : (ε*Real.sqrt (t : ℝ))^2 = ε^2*(t : ℝ) := by rw [mul_pow, hs]
  have h1 : 1 ≤ ε*Real.sqrt (t : ℝ) := by
    have hn : 0 ≤ ε*Real.sqrt (t : ℝ) := by positivity
    nlinarith
  have hh := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg (t : ℝ))
  nlinarith
private theorem tracking_upper {K : ℕ} (N : ℕ → Fin K → ℕ) (I : ℕ → Fin K)
    (hstep : ∀ t a, N (t+1) a = N t a + if a = I t then 1 else 0)
    (hsum : ∀ t, ∑ a, N t a = t)
    (w : Fin K → ℝ) (hw : ∀ a, 0 ≤ w a) (ε : ℝ) (hε : 0 < ε)
    (T : ℕ) (hT : 1 ≤ T)
    (hsel : ∀ t, T ≤ t → (N t (I t) : ℝ) ≤ (t : ℝ)*(w (I t)+ε)) :
    ∀ t, T ≤ t → ∀ a, (N t a : ℝ) ≤ (t : ℝ)*(w a+ε)+(T : ℝ) := by
  classical
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    intro a
    have ha : N T a ≤ T := (Finset.single_le_sum (fun b _ => Nat.zero_le (N T b)) (Finset.mem_univ a)).trans_eq (hsum T)
    have har : (N T a : ℝ) ≤ T := by exact_mod_cast ha
    have hh : 0 ≤ (T : ℝ)*(w a+ε) := mul_nonneg (Nat.cast_nonneg _) (add_nonneg (hw a) hε.le)
    linarith
  | succ t ht ih =>
    intro a
    rw [hstep]
    by_cases ha : a = I t
    · subst a; rw [if_pos rfl, Nat.cast_add, Nat.cast_one, Nat.cast_add, Nat.cast_one]
      have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
      nlinarith [hsel t ht, hw (I t)]
    · rw [if_neg ha, add_zero, Nat.cast_add, Nat.cast_one]
      nlinarith [ih a, hw a]
private theorem simplex_error {K : ℕ} (hK : 2 ≤ K) (v w : Fin K → ℝ)
    (hs : ∑ a, v a = ∑ a, w a) (ε : ℝ) (hε : 0 < ε)
    (hu : ∀ a, v a-w a ≤ 2*ε) : ∀ a, |v a-w a| ≤ 3*((K : ℝ)-1)*ε := by
  classical
  have hsum : ∑ a, (v a-w a) = 0 := by rw [Finset.sum_sub_distrib, hs, sub_self]
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  intro a
  have he := Finset.sum_erase_add Finset.univ (fun b => v b-w b) (Finset.mem_univ a)
  have hb : ∑ b ∈ Finset.univ.erase a, (v b-w b) ≤ ∑ _b ∈ Finset.univ.erase a, 2*ε :=
    Finset.sum_le_sum fun b _ => hu b
  have hc : (∑ _b ∈ Finset.univ.erase a, 2*ε) = ((K : ℝ)-1)*(2*ε) := by
    simp [Finset.card_erase_of_mem, Nat.cast_sub (by omega : 1 ≤ K)]
  rw [hc] at hb
  rw [hsum] at he
  apply abs_le.mpr
  constructor <;> nlinarith [hu a, mul_nonneg (by linarith : 0 ≤ (K : ℝ)-1) hε.le]

private theorem prefix_count {K : ℕ} (ω : ℕ → Fin K × ℝ) (t : ℕ) (a : Fin K) :
    armPullCount a (banditTrajPrefix K t ω) = trajPullCount a t ω := by
  classical
  unfold armPullCount
  rw [Set.toFinset_ofPred,Finset.card_filter]
  unfold trajPullCount
  rw [Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if (ω i).1=a then 1 else 0) t

private theorem prefix_mean {K : ℕ} (ω : ℕ → Fin K × ℝ) (t : ℕ) (a : Fin K) :
    armEmpiricalMean a (banditTrajPrefix K t ω) = trajEmpiricalMean a t ω := by
  classical
  unfold armEmpiricalMean
  rw [Set.toFinset_ofPred,Finset.sum_filter,prefix_count]
  unfold trajEmpiricalMean
  rw [Finset.sum_filter]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => if (ω i).1=a then (ω i).2 else 0) t

private theorem hist_mean_prefix {K : ℕ} (ω : ℕ → Fin K × ℝ) (t s : ℕ) (hs : s ≤ t) :
    histMeanAt (banditTrajPrefix K t ω) s = trajMeanVec s ω := by
  ext a
  dsimp [histMeanAt,trajMeanVec]
  have he : (fun i : Fin (min s t) => banditTrajPrefix K t ω (Fin.castLE (Nat.min_le_right s t) i)) = banditTrajPrefix K (min s t) ω := rfl
  rw [he,prefix_mean,Nat.min_eq_left hs]

private theorem count_step {K : ℕ} (ω : ℕ → Fin K × ℝ) (t : ℕ) (a : Fin K) :
    trajPullCount a (t+1) ω = trajPullCount a t ω + if a=(ω t).1 then 1 else 0 := by
  simp only [trajPullCount,Finset.range_add_one,Finset.filter_insert]
  by_cases ha : a=(ω t).1
  · simp [ha,Finset.mem_filter,Finset.mem_range]
  · simp [ha,Ne.symm ha]


private theorem count_sum {K : ℕ} (ω : ℕ → Fin K × ℝ) (t : ℕ) :
    ∑ a, trajPullCount a t ω = t := by
  induction t with
  | zero => simp [trajPullCount]
  | succ t ih => simp_rw [count_step]; rw [Finset.sum_add_distrib, ih]; simp
private theorem forced_choice {K : ℕ} (wt : (Fin K → ℝ) → Fin K → ℝ)
    (ω : ℕ → Fin K × ℝ) (hω : FollowsDTracking wt ω) (t : ℕ) (a : Fin K)
    (ha : (trajPullCount a t ω : ℝ) < Real.sqrt (t : ℝ)-(K : ℝ)/2) :
    trajPullCount (ω t).1 t ω ≤ trajPullCount a t ω := by
  have ham : a ∈ forcedSet (banditTrajPrefix K t ω) := by
    change (armPullCount a (banditTrajPrefix K t ω) : ℝ) < _
    simpa only [prefix_count] using ha
  rcases hω t with ⟨_, _, hmin⟩ | ⟨hem, _⟩
  · simpa only [prefix_count] using hmin a ham
  · rw [hem] at ham; exact False.elim ham
private theorem chosen_upper {K : ℕ} (wt : (Fin K → ℝ) → Fin K → ℝ)
    (hwt : ∀ μ, wt μ ∈ simplex K)
    (ω : ℕ → Fin K × ℝ) (hω : FollowsDTracking wt ω) (t : ℕ) :
    (trajPullCount (ω t).1 t ω : ℝ) ≤ max (Real.sqrt (t : ℝ)) ((t : ℝ)*wt (trajMeanVec t ω) (ω t).1) := by
  rcases hω t with ⟨_, hmem, _⟩ | ⟨_, hmax⟩
  · change (armPullCount (ω t).1 (banditTrajPrefix K t ω) : ℝ) < _ at hmem
    rw [prefix_count] at hmem
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    exact (by linarith : (trajPullCount (ω t).1 t ω : ℝ) ≤ Real.sqrt (t : ℝ)).trans (le_max_left _ _)
  · simp only [prefix_count, hist_mean_prefix ω t t le_rfl] at hmax
    have hsum : ∑ b, ((t : ℝ)*wt (trajMeanVec t ω) b - (trajPullCount b t ω : ℝ)) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, (hwt _).2]
      have hc : (∑ b, (trajPullCount b t ω : ℝ)) = (t : ℝ) := by exact_mod_cast count_sum ω t
      rw [hc]; ring
    have hn : 0 ≤ (t : ℝ)*wt (trajMeanVec t ω) (ω t).1 - (trajPullCount (ω t).1 t ω : ℝ) := by
      by_contra! hh
      have hneg : (∑ b, ((t : ℝ)*wt (trajMeanVec t ω) b - (trajPullCount b t ω : ℝ))) < ∑ _b : Fin K, (0 : ℝ) := by
        apply Finset.sum_lt_sum (fun b _ => (hmax b).trans hh.le)
        exact ⟨(ω t).1, Finset.mem_univ _, hh⟩
      simp only [hsum, Finset.sum_const_zero] at hneg
      linarith
    have hbound : (trajPullCount (ω t).1 t ω : ℝ) ≤ (t : ℝ)*wt (trajMeanVec t ω) (ω t).1 := by linarith
    exact hbound.trans (le_max_right _ _)

theorem linear_tracking {K : ℕ} (hK : 2≤K) (w : Fin K → ℝ) (hw : w∈simplex K)
    (wt : (Fin K → ℝ) → Fin K → ℝ) (hwt : ∀ μ, wt μ∈simplex K)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C B : ℝ, 0<C ∧ 0≤B ∧ ∀ (t₀ : ℕ) (ω : ℕ → Fin K × ℝ),
      FollowsDTracking wt ω → (∀ t, t₀≤t → ∀ a, |wt (trajMeanVec t ω) a-w a|≤ε) →
      ∀ t : ℕ, C*(t₀ : ℝ)+B≤(t : ℝ) → ∀ a,
        |(trajPullCount a t ω : ℝ)/(t : ℝ)-w a|≤3*((K : ℝ)-1)*ε := by
  obtain ⟨T₁,hT₁⟩ := exists_nat_gt (1/ε^2)
  let L := 1+1/ε
  let B₀ : ℝ := (T₁ : ℝ)+1
  have hL : 1≤L := by dsimp [L]; linarith [one_div_pos.mpr hε]
  have hLp : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hB : 0≤B₀ := by dsimp [B₀]; positivity
  refine ⟨L,L*B₀,hLp,mul_nonneg hLp.le hB,?_⟩
  intro t₀ ω hω hclose t ht
  let T := max t₀ (max 1 T₁)
  have hT0 : t₀≤T := le_max_left _ _
  have hT1 : 1≤T := (le_max_left _ _).trans (le_max_right _ _)
  have hT2 : T₁≤T := (le_max_right _ _).trans (le_max_right _ _)
  have hTr : 1/ε^2≤(T : ℝ) := hT₁.le.trans (by exact_mod_cast hT2)
  have hTbound : (T : ℝ)≤(t₀ : ℝ)+B₀ := by
    dsimp [T,B₀]
    rw [Nat.cast_max,Nat.cast_max,Nat.cast_one]
    apply max_le
    · linarith [Nat.cast_nonneg (α := ℝ) T₁]
    · apply max_le <;> linarith [Nat.cast_nonneg (α := ℝ) t₀,Nat.cast_nonneg (α := ℝ) T₁]
  have htT : T≤t := by
    have hm := mul_le_mul_of_nonneg_right hL (show 0≤(t₀ : ℝ)+B₀ by positivity)
    have ht' : (T : ℝ)≤t := hTbound.trans (by nlinarith)
    exact_mod_cast ht'
  have htp : (0 : ℝ)<t := by exact_mod_cast (hT1.trans htT)
  have hterr : (T : ℝ)≤ε*(t : ℝ) := by
    have hprod := mul_le_mul_of_nonneg_left ht hε.le
    have hident : ε*L=ε+1 := by dsimp [L]; field_simp [hε.ne']
    have hscale : ε*(L*(t₀ : ℝ)+L*B₀)=(ε+1)*((t₀ : ℝ)+B₀) := by rw [← mul_add,← mul_assoc,hident]
    rw [hscale] at hprod
    nlinarith [Nat.cast_nonneg (α := ℝ) t₀]
  have hsel : ∀ n, T≤n → (trajPullCount (ω n).1 n ω : ℝ)≤(n : ℝ)*(w (ω n).1+ε) := by
    intro n hn
    apply (chosen_upper wt hwt ω hω n).trans
    apply max_le
    · have hh := sqrt_small ε hε T hTr n hn
      have hw0 := hw.1 (ω n).1
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    · have hh := (abs_le.mp (hclose n (hT0.trans hn) (ω n).1)).2
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have hub := tracking_upper (fun n a => trajPullCount a n ω) (fun n => (ω n).1)
    (count_step ω) (count_sum ω) w hw.1 ε hε T hT1 hsel
  have hsum : (∑ a, (trajPullCount a t ω : ℝ)/(t : ℝ))=∑ a,w a := by
    rw [← Finset.sum_div,hw.2]
    have hc : (∑ b, (trajPullCount b t ω : ℝ))=(t : ℝ) := by exact_mod_cast count_sum ω t
    rw [hc,div_self htp.ne']
  apply simplex_error hK _ w hsum ε hε
  intro a
  have hh := (div_le_iff₀ htp).mpr
    (show (trajPullCount a t ω : ℝ)≤(w a+2*ε)*(t : ℝ) by nlinarith [hub t htT a])
  linarith

end DUniformProof


open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
set_option maxHeartbeats 1500000
namespace OptimalBAI.TrackStop.ExpFamily

lemma exp_lintegral (F : ExpFamily) (θ ℓ : ℝ) (hℓ : θ+ℓ ∈ F.Θ) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (ℓ*x)) ∂F.arm θ)=
      ENNReal.ofReal (Real.exp (F.b (θ+ℓ)-F.b θ)) := by
  have he x : ENNReal.ofReal (Real.exp (ℓ*x)) =
      ENNReal.ofReal (Real.exp (F.b (θ+ℓ)-F.b θ))*
        ENNReal.ofReal (Real.exp (ℓ*x-(F.b (θ+ℓ)-F.b θ))) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
    congr 2
    ring
  simp_rw [he]
  rw [lintegral_const_mul _ (by fun_prop),F.normalized_tilt _ _ hℓ,mul_one]

lemma exp_integrable (F : ExpFamily) (θ ℓ : ℝ) (hℓ : θ+ℓ ∈ F.Θ) :
    Integrable (fun x => Real.exp (ℓ*x)) (F.arm θ) := by
  refine ⟨by fun_prop,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x => (Real.exp_pos _).le)),
    F.exp_lintegral θ ℓ hℓ]
  exact ENNReal.ofReal_lt_top

lemma mgf_formula (F : ExpFamily) (θ ℓ : ℝ) (hℓ : θ+ℓ ∈ F.Θ) :
    mgf id (F.arm θ) ℓ=Real.exp (F.b (θ+ℓ)-F.b θ) := by
  rw [mgf]
  simp only [id_eq]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun x => (Real.exp_pos _).le))
    (by fun_prop)]
  rw [F.exp_lintegral θ ℓ hℓ,ENNReal.toReal_ofReal (Real.exp_pos _).le]

lemma zero_interior_integrableExp (F : ExpFamily) (θ : ℝ) (hθ : θ ∈ F.Θ) :
    (0 : ℝ) ∈ interior (integrableExpSet id (F.arm θ)) := by
  apply mem_interior_iff_mem_nhds.mpr
  have h : ∀ᶠ ℓ in 𝓝 (0 : ℝ), θ+ℓ ∈ F.Θ :=
    (continuous_const.add continuous_id).continuousAt.tendsto.eventually
      (by simpa using F.isOpen_Θ.mem_nhds hθ)
  exact h.mono (fun ℓ hℓ => F.exp_integrable θ ℓ hℓ)

lemma reward_integrable (F : ExpFamily) (θ : ℝ) (hθ : θ ∈ F.Θ) :
    Integrable id (F.arm θ) :=
  integrable_of_mem_interior_integrableExpSet (F.zero_interior_integrableExp θ hθ)

lemma mean_integral (F : ExpFamily) (θ : ℝ) (hθ : θ ∈ F.Θ) :
    (∫ x, x ∂F.arm θ)=deriv F.b θ := by
  have he : mgf id (F.arm θ) =ᶠ[𝓝 (0 : ℝ)] fun ℓ => Real.exp (F.b (θ+ℓ)-F.b θ) := by
    have h : ∀ᶠ ℓ in 𝓝 (0 : ℝ), θ+ℓ ∈ F.Θ :=
      (continuous_const.add continuous_id).continuousAt.tendsto.eventually
        (by simpa using F.isOpen_Θ.mem_nhds hθ)
    exact h.mono (fun ℓ hℓ => F.mgf_formula θ ℓ hℓ)
  have hd : HasDerivAt (fun ℓ : ℝ => Real.exp (F.b (θ+ℓ)-F.b θ)) (deriv F.b θ) 0 := by
    have hbd : HasDerivAt F.b (deriv F.b θ) (θ+id (0 : ℝ)) := by
      have hb0 : HasDerivAt F.b (deriv F.b θ) θ :=
        (F.toAllocationFamily.b_differentiableAt hθ).hasDerivAt
      simpa only [id_eq,add_zero] using hb0
    have hb := hbd.comp 0
      ((hasDerivAt_id (0 : ℝ)).const_add θ)
    have hx := (hb.sub_const (F.b θ)).exp
    simpa using hx
  change (∫ x, id x ∂F.arm θ)=_
  rw [← deriv_mgf_zero (F.zero_interior_integrableExp θ hθ),he.deriv_eq,hd.deriv]

end OptimalBAI.TrackStop.ExpFamily


open MeasureTheory InformationTheory
open scoped ENNReal
set_option maxHeartbeats 1500000
namespace OptimalBAI.TrackStop.ExpFamily

lemma relative_arm (F : ExpFamily) (θ φ : ℝ) :
    (F.arm φ).withDensity (fun x => ENNReal.ofReal
      (Real.exp ((θ-φ)*x-(F.b θ-F.b φ))))=F.arm θ := by
  rw [arm,← withDensity_mul _ (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  rw [Pi.mul_apply,← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  ring

lemma arm_ac (F : ExpFamily) (θ φ : ℝ) : F.arm θ ≪ F.arm φ := by
  rw [← F.relative_arm θ φ]
  exact withDensity_absolutelyContinuous _ _

lemma llr_arm (F : ExpFamily) (θ φ : ℝ) (hφ : φ ∈ F.Θ) :
    llr (F.arm θ) (F.arm φ) =ᵐ[F.arm θ]
      fun x => (θ-φ)*x-(F.b θ-F.b φ) := by
  letI := F.isProbabilityMeasure_arm hφ
  have hrn := Measure.rnDeriv_withDensity (F.arm φ)
    (f := fun x => ENNReal.ofReal (Real.exp ((θ-φ)*x-(F.b θ-F.b φ)))) (by fun_prop)
  rw [F.relative_arm] at hrn
  filter_upwards [(F.arm_ac θ φ).ae_le hrn] with x hx
  simp only [llr_def,hx,ENNReal.toReal_ofReal (Real.exp_pos _).le,Real.log_exp]

lemma kl_parameter (F : ExpFamily) (θ φ : ℝ) (hθ : θ ∈ F.Θ) (hφ : φ ∈ F.Θ) :
    klDiv (F.arm θ) (F.arm φ)=
      ENNReal.ofReal (F.b φ-F.b θ-deriv F.b θ*(φ-θ)) := by
  letI := F.isProbabilityMeasure_arm hθ
  letI := F.isProbabilityMeasure_arm hφ
  have haff : Integrable (fun x => (θ-φ)*x-(F.b θ-F.b φ)) (F.arm θ) :=
    ((F.reward_integrable θ hθ).const_mul (θ-φ)).sub (integrable_const _)
  have hi : Integrable (llr (F.arm θ) (F.arm φ)) (F.arm θ) :=
    haff.congr (F.llr_arm θ φ hφ).symm
  have hlin : Integrable (fun x : ℝ => (θ-φ)*x) (F.arm θ) :=
    (F.reward_integrable θ hθ).const_mul (θ-φ)
  rw [klDiv_of_ac_of_integrable (F.arm_ac θ φ) hi,
    integral_congr_ae (F.llr_arm θ φ hφ),integral_sub
      hlin (integrable_const _),
    integral_const_mul,F.mean_integral θ hθ]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,add_sub_cancel_right]
  congr 1
  ring

lemma kl_means (F : ExpFamily) (u v : ℝ) (hu : u ∈ F.M) (hv : v ∈ F.M) :
    klDiv (F.arm (F.θof u)) (F.arm (F.θof v))=ENNReal.ofReal (F.d u v) := by
  have hp : F.θof u ∈ F.Θ := F.toAllocationFamily.parameter_mem hu
  have hq : F.θof v ∈ F.Θ := F.toAllocationFamily.parameter_mem hv
  rw [F.kl_parameter _ _ hp hq]
  have hm : deriv F.b (F.θof u)=u := F.toAllocationFamily.mean_parameter hu
  change ENNReal.ofReal (F.b (F.θof v)-F.b (F.θof u)-deriv F.b (F.θof u)*(F.θof v-F.θof u))=_
  rw [hm]
  rfl

end OptimalBAI.TrackStop.ExpFamily


open MeasureTheory InformationTheory BanditAlgorithm Filter Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1500000
namespace OptimalBAI.TrackStop

lemma bandit_means {K : ℕ} (F : ExpFamily) (θ : Fin K → F.Θ) :
    banditArmMean (expFamilyBandit F θ)=meanVec F θ := by
  funext a
  exact F.mean_integral (θ a) (θ a).2

lemma optimalArms_eq_best {K : ℕ} (F : ExpFamily) (θ : Fin K → F.Θ) (hθ : θ∈Sθ F K) :
    banditOptimalArms (expFamilyBandit F θ)={a | IsBest (meanVec F θ) a} := by
  obtain ⟨a,ha⟩ := hθ
  letI : Nonempty (Fin K) := ⟨a⟩
  have hbest : IsBest (meanVec F θ) a := ha
  have hmax : banditOptimalMean (expFamilyBandit F θ)=meanVec F θ a := by
    rw [banditOptimalMean,bandit_means]
    apply le_antisymm
    · apply ciSup_le
      intro i
      by_cases hi : i=a
      · simp [hi]
      · exact (hbest i hi).le
    · exact le_ciSup (Set.finite_range (meanVec F θ)).bddAbove a
  ext i
  change banditArmMean (expFamilyBandit F θ) i=banditOptimalMean (expFamilyBandit F θ) ↔ _
  rw [bandit_means,hmax]
  constructor
  · intro hi
    have hie : i=a := by
      by_contra hne
      exact (ne_of_lt (hbest i hne)) hi
    simpa [hie] using hbest
  · intro hi
    have hie : i=a := isBest_unique hi hbest
    rw [hie]

noncomputable def parametersOfMeans {K : ℕ} (F : ExpFamily) (lam : Fin K → ℝ)
    (hlam : ∀ a, lam a∈F.M) : Fin K → F.Θ :=
  fun a => ⟨F.θof (lam a),F.toAllocationFamily.parameter_mem (hlam a)⟩

lemma parameters_mean {K : ℕ} (F : ExpFamily) (lam : Fin K → ℝ)
    (hlam : ∀ a, lam a∈F.M) : meanVec F (parametersOfMeans F lam hlam)=lam := by
  funext a
  exact F.toAllocationFamily.mean_parameter (hlam a)

lemma parameter_model_alternative {K : ℕ} (F : ExpFamily) (θ : Fin K → F.Θ)
    (hθ : θ∈Sθ F K) (lam : Fin K → ℝ) (hlam : lam∈Alt F (meanVec F θ)) :
    expFamilyBandit F (parametersOfMeans F lam hlam.1.1)∈
      baiAlternatives (modelClass F K) (expFamilyBandit F θ) := by
  let φ := parametersOfMeans F lam hlam.1.1
  have hφ : φ∈Sθ F K := by
    change ∃ a, IsBest (meanVec F φ) a
    rw [parameters_mean]
    exact hlam.1.2
  refine ⟨⟨φ,hφ,rfl⟩,?_⟩
  rw [optimalArms_eq_best F θ hθ,optimalArms_eq_best F φ hφ,parameters_mean]
  apply Set.disjoint_left.mpr
  intro a ha hb
  exact hlam.2 a ha hb

lemma alternative_information {K : ℕ} (F : ExpFamily) (θ : Fin K → F.Θ)
    (lam : Fin K → ℝ) (hlam : ∀ a, lam a∈F.M) (α : Fin K → ℝ≥0) :
    (∑ a, (α a : ℝ≥0∞)*klDiv ((expFamilyBandit F θ).P a)
      ((expFamilyBandit F (parametersOfMeans F lam hlam)).P a)) =
    ENNReal.ofReal (∑ a, (α a : ℝ)*F.d (meanVec F θ a) (lam a)) := by
  have hk a : klDiv ((expFamilyBandit F θ).P a)
      ((expFamilyBandit F (parametersOfMeans F lam hlam)).P a)=
      ENNReal.ofReal (F.d (meanVec F θ a) (lam a)) := by
    have ht : F.θof (meanVec F θ a)=(θ a : ℝ) :=
      F.toAllocationFamily.parameter_mean (θ a).2
    have hkm := F.kl_means (meanVec F θ a) (lam a)
      (show meanVec F θ a∈F.M from ⟨θ a,(θ a).2,rfl⟩) (hlam a)
    rw [ht] at hkm
    exact hkm
  simp_rw [hk]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [ENNReal.ofReal_mul (α a).coe_nonneg,ENNReal.ofReal_coe_nnreal]
  · intro a ha
    exact mul_nonneg (α a).coe_nonneg (F.toAllocationFamily.d_nonneg ⟨θ a,(θ a).2,rfl⟩ (hlam a))

lemma complexity_lower (F : ExpFamily) {K : ℕ} (θ : Fin K → F.Θ) (hθ : θ∈Sθ F K)
    (w : Fin K → ℝ) (hw : IsOptimalProportion F (meanVec F θ) w)
    (I : ℝ) (hI : 0≤I) (hcost : transportCost F (meanVec F θ) w=(I : EReal)) :
    (ENNReal.ofReal I)⁻¹≤baiComplexity (expFamilyBandit F θ) (modelClass F K) := by
  unfold baiComplexity
  apply ENNReal.inv_le_inv.mpr
  apply iSup_le
  intro α
  apply iSup_le
  intro hα
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hfin
  let v : Fin K → ℝ := fun a => α a
  change ∑ i, α i=1 at hα
  have hv : v∈simplex K := ⟨fun a => (α a).coe_nonneg,by dsimp [v]; exact_mod_cast hα⟩
  have hlow := hw.2 v hv
  rw [hcost] at hlow
  have hlt : transportCost F (meanVec F θ) v < ((I+(ε : ℝ) : ℝ) : EReal) :=
    hlow.trans_lt (EReal.coe_lt_coe_iff.mpr (by exact_mod_cast lt_add_of_pos_right I hε))
  obtain ⟨lam,h⟩ := iInf_lt_iff.mp hlt
  obtain ⟨hlam,hval⟩ := iInf_lt_iff.mp h
  have had := parameter_model_alternative F θ hθ lam hlam
  have hh : (⨅ ν'∈baiAlternatives (modelClass F K) (expFamilyBandit F θ),
      ∑ a, (α a : ℝ≥0∞)*klDiv ((expFamilyBandit F θ).P a) (ν'.P a)) ≤
      ∑ a, (α a : ℝ≥0∞)*klDiv ((expFamilyBandit F θ).P a)
        ((expFamilyBandit F (parametersOfMeans F lam hlam.1.1)).P a) :=
    iInf_le_of_le (expFamilyBandit F (parametersOfMeans F lam hlam.1.1))
    (iInf_le_of_le had le_rfl)
  apply hh.trans
  rw [alternative_information F θ lam hlam.1.1 α]
  have hvle : (∑ a, (α a : ℝ)*F.d (meanVec F θ a) (lam a)) ≤ I+(ε : ℝ) :=
    (EReal.coe_lt_coe_iff.mp hval).le
  calc
    _ ≤ ENNReal.ofReal (I+(ε : ℝ)) := ENNReal.ofReal_le_ofReal hvle
    _ = ENNReal.ofReal I+ε := by rw [ENNReal.ofReal_add hI ε.coe_nonneg,ENNReal.ofReal_coe_nnreal]

end OptimalBAI.TrackStop


open Filter Topology
set_option maxHeartbeats 1500000
namespace OptimalBAI.TrackStop

lemma exists_information (F : ExpFamily) {K : ℕ} (hK : 2≤K)
    (μ : Fin K → ℝ) (hμ : μ∈bestArmMeans F K) (w : Fin K → ℝ)
    (hw : IsOptimalProportion F μ w) :
    ∃ (best : Fin K) (I : ℝ), IsBest μ best ∧ 0<I ∧
      transportCost F μ w=(I : EReal) ∧ ∀ b, b≠best →
        I≤OptProportions.pairCost F.toAllocationFamily (μ best) (μ b) (w best) (w b) := by
  letI : NeZero K := ⟨by omega⟩
  obtain ⟨best,hbest⟩ := hμ.2
  let e := Equiv.swap (0 : Fin K) best
  have he0 : e 0=best := by simp [e]
  have hm0 : IsBest (μ∘e) 0 := (isBest_reindex e μ 0).mpr (by simpa [he0] using hbest)
  have hwpos := optimal_weights_positive F hK μ hμ w hw
  let I := finiteCost hK F (μ∘e) (w∘e)
  have hc : transportCost F μ w=(I : EReal) := by
    rw [← transportCost_reindex e F μ w]
    exact transportCost_eq_finiteCost hK F (μ∘e) (w∘e) (fun a => hμ.1 (e a)) hm0
      ((simplex_reindex e w).mpr hw.1)
  have hI : 0<I := by
    unfold I finiteCost
    rw [Finset.lt_inf'_iff]
    intro b hb
    have hb0 : b≠0 := (Finset.mem_erase.mp hb).1
    exact OptProportions.pairCost_pos F.toAllocationFamily (hμ.1 (e 0)) (hμ.1 (e b))
      (hm0 b hb0) (hwpos _) (hwpos _)
  refine ⟨best,I,hbest,hI,hc,?_⟩
  intro b hb
  have hb0 : e.symm b≠0 := by
    intro he
    have hh := congrArg e he
    simp only [e.apply_symm_apply,he0] at hh
    exact hb hh
  have hh := Finset.inf'_le
    (fun a => OptProportions.pairCost F.toAllocationFamily ((μ∘e) 0) ((μ∘e) a) ((w∘e) 0) ((w∘e) a))
    (Finset.mem_erase.mpr ⟨hb0,Finset.mem_univ (e.symm b)⟩)
  simpa only [I,finiteCost,Function.comp_apply,e.apply_symm_apply,he0] using hh

end OptimalBAI.TrackStop


open BanditAlgorithm Filter Topology
set_option maxHeartbeats 1500000
namespace OptimalBAI.TrackStop

lemma uniform_information (F : ExpFamily) {K : ℕ} (hK : 2≤K)
    (μ w : Fin K → ℝ) (hμ : μ∈bestArmMeans F K) (hw : IsOptimalProportion F μ w)
    (wt : (Fin K → ℝ) → Fin K → ℝ) (hwt : ∀ m, wt m∈simplex K)
    (hwtopt : ∀ m∈bestArmMeans F K, IsOptimalProportion F m (wt m))
    (best : Fin K) (hbest : IsBest μ best) (I c : ℝ) (hc : c<I)
    (hpair : ∀ b, b≠best → I≤OptProportions.pairCost F.toAllocationFamily (μ best) (μ b) (w best) (w b)) :
    ∃ ρ C B : ℝ, 0<ρ ∧ 0<C ∧ 0≤B ∧ ∀ t₀ : ℕ, ∀ ω : ℕ → Fin K × ℝ,
      (FollowsCTracking wt ω ∨ FollowsDTracking wt ω) →
      (∀ t : ℕ, t₀≤t → ∀ a, |trajMeanVec t ω a-μ a|≤ρ) →
      ∀ t : ℕ, C*(t₀ : ℝ)+B≤(t : ℝ) → 1≤t ∧
        ∀ β : ℝ, β<c*(t : ℝ) → ∀ b, b≠best →
          glrDen F best b t ω+(β : EReal)<glrNum F best b t ω := by
  have hKr : (2 : ℝ)≤K := by exact_mod_cast hK
  have hKp : (0 : ℝ)<K := by linarith
  have hwpos := optimal_weights_positive F hK μ hμ w hw
  obtain ⟨η,hη,hlocal⟩ := local_information F μ w hμ.1 hwpos best hbest I hpair c hc
  let ε := η/(6*(K : ℝ))
  have hε : 0<ε := by dsimp [ε]; positivity
  have hCε : 3*ε≤η := by dsimp [ε]; rw [←mul_div_assoc]; apply (div_le_iff₀ (by positivity : 0<6*(K : ℝ))).mpr; nlinarith
  have hDε : 3*((K : ℝ)-1)*ε≤η := by
    dsimp [ε]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<6*(K : ℝ))).mpr
    nlinarith
  obtain ⟨ρ,hρ,htarget⟩ := target_local F hK μ w hμ hw wt hwt hwtopt ε hε
  obtain ⟨CC,BC,hCC,hBC,hC⟩ := c_tracking_linear wt hwt w hw.1 ε hε
  obtain ⟨CD,BD,hCD,hBD,hD⟩ := DUniformProof.linear_tracking hK w hw.1 wt hwt ε hε
  let C := max 1 (max CC CD)
  let B := max 1 (max BC BD)
  have hC1 : 1≤C := le_max_left _ _
  have hB1 : 1≤B := le_max_left _ _
  have hCCC : CC≤C := (le_max_left _ _).trans (le_max_right _ _)
  have hCCD : CD≤C := (le_max_right _ _).trans (le_max_right _ _)
  have hBBC : BC≤B := (le_max_left _ _).trans (le_max_right _ _)
  have hBBD : BD≤B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨min ρ η,C,B,lt_min hρ hη,by linarith,by linarith,?_⟩
  intro t₀ ω hω hm t ht
  have ht0 : t₀≤t := by
    have hh := mul_le_mul_of_nonneg_right hC1 (Nat.cast_nonneg (α := ℝ) t₀)
    have hr : (t₀ : ℝ)≤(t : ℝ) := by nlinarith
    exact_mod_cast hr
  have ht1 : 1≤t := by
    have hh := mul_nonneg (show 0≤C by linarith) (Nat.cast_nonneg (α := ℝ) t₀)
    have hr : (1 : ℝ)≤t := by linarith
    exact_mod_cast hr
  have hv : ∀ n : ℕ, t₀≤n → ∀ a, |wt (trajMeanVec n ω) a-w a|≤ε := by
    intro n hn
    exact htarget _ (fun a => (hm n hn a).trans (min_le_left _ _))
  have hp : ∀ a, |(trajPullCount a t ω : ℝ)/(t : ℝ)-w a|≤η := by
    rcases hω with hω | hω
    · have hh : CC*(t₀ : ℝ)+BC≤(t : ℝ) := by nlinarith [mul_le_mul_of_nonneg_right hCCC (Nat.cast_nonneg (α := ℝ) t₀)]
      exact fun a => (hC t₀ ω hω hv t hh a).trans hCε
    · have hh : CD*(t₀ : ℝ)+BD≤(t : ℝ) := by nlinarith [mul_le_mul_of_nonneg_right hCCD (Nat.cast_nonneg (α := ℝ) t₀)]
      exact fun a => (hD t₀ ω hω hv t hh a).trans hDε
  have hloc := hlocal (trajMeanVec t ω) (fun a => (trajPullCount a t ω : ℝ)/(t : ℝ))
    (fun a => (hm t ht0 a).trans (min_le_right _ _)) hp
  have htp : (0 : ℝ)<t := by exact_mod_cast ht1
  have hcounts (a : Fin K) : 0<trajPullCount a t ω := by
    have hh := hloc.1 a |>.2
    have hh' := (div_pos_iff.mp hh)
    rcases hh' with hh' | hh'
    · exact_mod_cast hh'.1
    · linarith
  refine ⟨ht1,?_⟩
  intro β hβ b hb
  apply glr_trigger_of_cost F best b t ω (hcounts best) (hcounts b) (hloc.1 best).1 (hloc.1 b).1
    (hloc.2.1 b hb).le β
  have hscale := pairCost_scaling F (trajEmpiricalMean best t ω) (trajEmpiricalMean b t ω)
    ((trajPullCount best t ω : ℝ)/(t : ℝ)) ((trajPullCount b t ω : ℝ)/(t : ℝ)) (t : ℝ)
    htp.ne' ((add_pos (hloc.1 best).2 (hloc.1 b).2).ne')
  simp only [mul_div_cancel₀ _ htp.ne'] at hscale
  rw [hscale]
  have hh := mul_lt_mul_of_pos_right (hloc.2.2 b hb) htp
  simp only [trajMeanVec] at hh
  nlinarith

end OptimalBAI.TrackStop


open MeasureTheory BanditAlgorithm Filter Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1500000
namespace OptimalBAI.TrackStop

lemma expected_log_bound (F : ExpFamily) {K : ℕ} (θ : Fin K → F.Θ) (π : BanditPolicy K)
    (α : ℝ) (r : ℕ → ℝ) (hr_pos : ∀ t,0<r t)
    (D : ℝ) (hD : 0<D) (hr : ∀ t : ℕ,1≤t → r t≤D*(t : ℝ)^α)
    (c A C B : ℝ) (hc : 0<c) (hA : 1/c<A) (hC : 0<C) (hB : 0≤B)
    (t₀ : (ℕ → Fin K × ℝ) → ℕ) (ht₀m : Measurable t₀)
    (ht₀i : (∫⁻ ω,(t₀ ω : ℝ≥0∞) ∂banditTrajMeasure (expFamilyBandit F θ) π)≠⊤)
    (hpath : ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F θ) π, ∀ n : ℕ,
      C*(t₀ ω : ℝ)+B≤(n : ℝ) → 1≤n ∧
        ∀ β : ℝ, β<c*(n : ℝ) → ∃ a, ∀ b,b≠a →
          glrDen F a b n ω+(β : EReal)<glrNum F a b n ω) :
    ∃ M : ℝ≥0∞, M≠⊤ ∧ ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      (∫⁻ ω,(chernoffTime F (rateThreshold r δ) ω : ℝ≥0∞)
        ∂banditTrajMeasure (expFamilyBandit F θ) π)≤M+(Nat.ceil (A*Real.log (1/δ)) : ℝ≥0∞) := by
  let P := banditTrajMeasure (expFamilyBandit F θ) π
  let H := fun ω => Nat.ceil (C*(t₀ ω : ℝ)+B)
  have ht₀R : Measurable (fun ω => (t₀ ω : ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp ht₀m
  have hHb : ∀ ω, (H ω : ℝ≥0∞)≤ENNReal.ofReal C*(t₀ ω : ℝ≥0∞)+ENNReal.ofReal (B+1) := by
    intro ω
    have hnon : 0≤C*(t₀ ω : ℝ)+B := by positivity
    have hh := (Nat.ceil_lt_add_one hnon).le
    have hh' := ENNReal.ofReal_le_ofReal hh
    simpa only [H,ENNReal.ofReal_natCast,add_assoc,
      ENNReal.ofReal_add (mul_nonneg hC.le (Nat.cast_nonneg _)) (by linarith : 0≤B+1),
      ENNReal.ofReal_mul hC.le] using hh'
  have hHi : (∫⁻ ω,(H ω : ℝ≥0∞) ∂P)≠⊤ := by
    apply ne_top_of_le_ne_top _ (lintegral_mono hHb)
    rw [lintegral_add_right _ measurable_const,lintegral_const_mul _ ht₀R,lintegral_const]
    simp only [measure_univ,mul_one]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ht₀i,ENNReal.ofReal_ne_top⟩
  refine ⟨∫⁻ ω,(H ω : ℝ≥0∞) ∂P,hHi,?_⟩
  filter_upwards [threshold_above_ceil α r hr_pos D hD hr c A hc hA] with δ hδ
  have hb : ∀ᵐ ω ∂P, (chernoffTime F (rateThreshold r δ) ω : ℝ≥0∞)≤
      (H ω : ℝ≥0∞)+(Nat.ceil (A*Real.log (1/δ)) : ℝ≥0∞) := by
    filter_upwards [hpath] with ω hω
    let n := H ω+Nat.ceil (A*Real.log (1/δ))
    have hlarge : C*(t₀ ω : ℝ)+B≤(n : ℝ) := by
      have hh : C*(t₀ ω : ℝ)+B≤(H ω : ℝ) := Nat.le_ceil _
      exact hh.trans (by dsimp [n]; exact_mod_cast (Nat.le_add_right (H ω) (Nat.ceil (A*Real.log (1/δ)))))
    have hpn := hω n hlarge
    have hnδ : Nat.ceil (A*Real.log (1/δ))≤n := Nat.le_add_left _ _
    have hτ := chernoff_le_of_trigger F (rateThreshold r δ) ω n hpn.1
      (hpn.2 _ (hδ.2 n hnδ))
    simpa only [n,Nat.cast_add,ENat.toENNReal_add,ENat.toENNReal_coe] using ENat.toENNReal_mono hτ
  have hh := lintegral_mono_ae hb
  rwa [lintegral_add_right _ measurable_const,lintegral_const,measure_univ,mul_one] at hh

lemma expected_ratio_limsup {f : ℝ → ℝ≥0∞} (M : ℝ≥0∞) (hM : M≠⊤)
    (A : ℝ) (hA : 0<A)
    (hb : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), f δ≤M+(Nat.ceil (A*Real.log (1/δ)) : ℝ≥0∞)) :
    limsup (fun δ : ℝ => f δ/ENNReal.ofReal (Real.log (1/δ))) (𝓝[>] (0 : ℝ))≤ENNReal.ofReal A := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hfin
  have hεR : (0 : ℝ)<ε := by exact_mod_cast hε
  have hconst : Tendsto (fun δ : ℝ => M.toReal/Real.log (1/δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using
      tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp log_inv_tendsto)
  have hn : Tendsto (fun δ : ℝ => (Nat.ceil (A*Real.log (1/δ)) : ℝ)/Real.log (1/δ))
      (𝓝[>] (0 : ℝ)) (𝓝 A) :=
    (tendsto_nat_ceil_mul_div_atTop hA.le).comp log_inv_tendsto
  have hr : Tendsto (fun δ : ℝ => (M.toReal+(Nat.ceil (A*Real.log (1/δ)) : ℝ))/Real.log (1/δ))
      (𝓝[>] (0 : ℝ)) (𝓝 A) := by
    simpa only [add_div,zero_add] using hconst.add hn
  apply limsup_le_of_le (by isBoundedDefault)
  filter_upwards [hb,hr.eventually (eventually_lt_nhds (show A<A+(ε : ℝ) by linarith)),
    log_inv_tendsto.eventually_gt_atTop 0] with δ hδ hratio hlog
  calc
    _≤(M+(Nat.ceil (A*Real.log (1/δ)) : ℝ≥0∞))/ENNReal.ofReal (Real.log (1/δ)) := by gcongr
    _=ENNReal.ofReal ((M.toReal+(Nat.ceil (A*Real.log (1/δ)) : ℝ))/Real.log (1/δ)) := by
      rw [ENNReal.ofReal_div_of_pos hlog,ENNReal.ofReal_add ENNReal.toReal_nonneg (Nat.cast_nonneg _),
        ENNReal.ofReal_toReal hM,ENNReal.ofReal_natCast]
    _≤ENNReal.ofReal (A+(ε : ℝ)) := ENNReal.ofReal_le_ofReal hratio.le
    _=ENNReal.ofReal A+ε := by rw [ENNReal.ofReal_add hA.le ε.coe_nonneg,ENNReal.ofReal_coe_nnreal]

end OptimalBAI.TrackStop


open MeasureTheory BanditAlgorithm Filter Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1500000
namespace OptimalBAI.TrackStop

lemma expected_asymptotic (F : ExpFamily) {K : ℕ} (hK : 2≤K)
    (θ : Fin K → F.Θ) (hθ : θ∈Sθ F K)
    (α : ℝ) (hα : α∈Set.Icc (1 : ℝ) (Real.exp 1/2))
    (r : ℕ → ℝ) (hr_pos : ∀ t,0<r t)
    (hr : ∃ D : ℝ,∀ t : ℕ,1≤t → r t≤D*(t : ℝ)^α)
    (wt : (Fin K → ℝ) → Fin K → ℝ) (hwt : ∀ μ',wt μ'∈simplex K)
    (hwtopt : ∀ μ'∈bestArmMeans F K,IsOptimalProportion F μ' (wt μ'))
    (π : BanditPolicy K) (hπ : IsCTrackingPolicy wt π ∨ IsDTrackingPolicy wt π) :
    limsup (fun δ : ℝ =>
      (∫⁻ ω,(chernoffTime F (rateThreshold r δ) ω : ℝ≥0∞)
        ∂banditTrajMeasure (expFamilyBandit F θ) π)/ENNReal.ofReal (Real.log (1/δ)))
      (𝓝[>] (0 : ℝ))≤ENNReal.ofReal α*baiComplexity (expFamilyBandit F θ) (modelClass F K) := by
  let μ := meanVec F θ
  have hμ : μ∈bestArmMeans F K := ⟨fun a => ⟨θ a,(θ a).2,rfl⟩,hθ⟩
  let w := wt μ
  have hw : IsOptimalProportion F μ w := hwtopt μ hμ
  obtain ⟨best,I,hbest,hI,hcost,hpair⟩ := exists_information F hK μ hμ w hw
  obtain ⟨D,hD⟩ := hr
  have hDp : 0<D := by
    have hd := hD 1 (by norm_num)
    norm_num at hd
    exact (hr_pos 1).trans_le hd
  have hfollow : ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F θ) π,
      FollowsCTracking wt ω ∨ FollowsDTracking wt ω := by
    rcases hπ with hC | hD
    · exact (policy_follows_C (expFamilyBandit F θ) π wt hC).mono (fun _ h => Or.inl h)
    · exact (policy_follows_D (expFamilyBandit F θ) π wt hD).mono (fun _ h => Or.inr h)
  have hstrong : limsup (fun δ : ℝ =>
      (∫⁻ ω,(chernoffTime F (rateThreshold r δ) ω : ℝ≥0∞)
        ∂banditTrajMeasure (expFamilyBandit F θ) π)/ENNReal.ofReal (Real.log (1/δ)))
      (𝓝[>] (0 : ℝ))≤ENNReal.ofReal (1/I) := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε hfin
    have hεR : (0 : ℝ)<ε := by exact_mod_cast hε
    let A := 1/I+(ε : ℝ)/2
    have hAp : 0<A := by dsimp [A]; positivity
    have hAI : 1/I<A := by dsimp [A]; linarith
    have hIA : 1/A<I := by
      have hh := (div_lt_iff₀ hI).mp hAI
      exact (div_lt_iff₀ hAp).mpr (by nlinarith)
    let c := (1/A+I)/2
    have hc : 0<c := by dsimp [c]; positivity
    have hcI : c<I := by dsimp [c]; linarith
    have hcA : 1/c<A := by
      have hh : 1/A<c := by dsimp [c]; linarith
      have hh' := (div_lt_iff₀ hAp).mp hh
      exact (div_lt_iff₀ hc).mpr (by nlinarith)
    obtain ⟨ρ,C,B,hρ,hC,hB,huniform⟩ := uniform_information F hK μ w hμ hw wt hwt hwtopt best hbest I c hcI hpair
    obtain ⟨t₀,ht₀m,ht₀i,hmeans⟩ := integrable_settling F hK θ hθ w hw wt hwt hwtopt π hπ ρ hρ
    have hpath : ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F θ) π,∀ n : ℕ,
        C*(t₀ ω : ℝ)+B≤(n : ℝ) → 1≤n ∧
          ∀ β : ℝ,β<c*(n : ℝ) → ∃ a,∀ b,b≠a →
            glrDen F a b n ω+(β : EReal)<glrNum F a b n ω := by
      filter_upwards [hfollow,hmeans] with ω hf hm
      intro n hn
      have hh := huniform (t₀ ω) ω hf hm n hn
      exact ⟨hh.1,fun β hβ => ⟨best,hh.2 β hβ⟩⟩
    obtain ⟨M,hM,hbound⟩ := expected_log_bound F θ π α r hr_pos D hDp hD c A C B hc hcA hC hB t₀ ht₀m ht₀i hpath
    have hlim := expected_ratio_limsup M hM A hAp hbound
    apply hlim.trans
    calc
      ENNReal.ofReal A≤ENNReal.ofReal (1/I+(ε : ℝ)) := ENNReal.ofReal_le_ofReal (by dsimp [A]; linarith)
      _=ENNReal.ofReal (1/I)+ε := by rw [ENNReal.ofReal_add (one_div_pos.mpr hI).le ε.coe_nonneg,ENNReal.ofReal_coe_nnreal]
  have hcomp := complexity_lower F θ hθ w hw I hI.le hcost
  have hinv : ENNReal.ofReal (1/I)=(ENNReal.ofReal I)⁻¹ := by
    rw [one_div,ENNReal.ofReal_inv_of_pos hI]
  rw [hinv] at hstrong
  apply hstrong.trans
  calc
    _≤baiComplexity (expFamilyBandit F θ) (modelClass F K) := hcomp
    _=1*baiComplexity (expFamilyBandit F θ) (modelClass F K) := (one_mul _).symm
    _≤_ := by gcongr; simpa using ENNReal.ofReal_le_ofReal hα.1

end OptimalBAI.TrackStop

open MeasureTheory BanditAlgorithm Filter Topology
open scoped ENNReal
open OptimalBAI.TrackStop
theorem solution (F : ExpFamily) {K : ℕ} (hK : 2 ≤ K)
    (θ : Fin K → F.Θ) (hθ : θ ∈ Sθ F K)
    (α : ℝ) (hα : α ∈ Set.Icc (1 : ℝ) (Real.exp 1 / 2))
    (r : ℕ → ℝ) (hr_pos : ∀ t, 0 < r t)
    (hr : ∃ D : ℝ, ∀ t : ℕ, 1 ≤ t → r t ≤ D * (t : ℝ) ^ α)
    (wt : (Fin K → ℝ) → (Fin K → ℝ)) (hwt_simplex : ∀ μ', wt μ' ∈ simplex K)
    (hwt_opt : ∀ μ' ∈ bestArmMeans F K, IsOptimalProportion F μ' (wt μ'))
    (π : BanditPolicy K) (hπ : IsCTrackingPolicy wt π ∨ IsDTrackingPolicy wt π) :
    limsup (fun δ : ℝ =>
        (∫⁻ ω, (chernoffTime F (rateThreshold r δ) ω : ℝ≥0∞)
            ∂banditTrajMeasure (expFamilyBandit F θ) π) /
          ENNReal.ofReal (Real.log (1 / δ))) (𝓝[>] (0 : ℝ)) ≤
      ENNReal.ofReal α * baiComplexity (expFamilyBandit F θ) (modelClass F K) := by
  exact expected_asymptotic F hK θ hθ α hα r hr_pos hr wt hwt_simplex hwt_opt π hπ

#print axioms solution
