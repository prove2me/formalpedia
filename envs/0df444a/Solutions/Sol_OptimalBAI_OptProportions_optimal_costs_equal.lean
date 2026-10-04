-- Prove2me | solution 1 for OptimalBAI.OptProportions.optimal_costs_equal
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T09:49:14.904235+00:00
-- url     : https://prove2.me/submissions/2aa42564-5653-452e-a080-4d841a476ff4

import Mathlib
import Definitions.Def_OptimalBAI_OptProportions_ExpFamily
import Definitions.Def_OptimalBAI_OptProportions_OptimalProportions



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

open OptimalBAI.OptProportions
theorem solution {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ)
    (hK : 2 ≤ K) (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0)
    (w : Fin K → ℝ) (hw : IsOptimalProportion F μ w) (a b : Fin K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (w 0 + w a) * jensenShannon F (w 0 / (w 0 + w a)) (μ 0) (μ a) =
      (w 0 + w b) * jensenShannon F (w 0 / (w 0 + w b)) (μ 0) (μ b) := by
  simpa only [pairCost] using optimal_pair_costs_equal F μ hK hμ hbest w hw a b ha hb

#print axioms solution
