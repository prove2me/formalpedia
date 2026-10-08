-- Prove2me | solution 1 for OptimalBAI.LowerBound.sample_complexity_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T16:33:46.036646+00:00
-- url     : https://prove2.me/submissions/c518ec0d-3c5f-4eab-a97a-7d53ae5a5dca

/- Released under Apache 2.0 license. Written by Codex. -/
import Mathlib
import Definitions.Def_OptimalBAI_LowerBound_ExpFamily
import Definitions.Def_OptimalBAI_LowerBound_IsDeltaPAC
import Definitions.Def_OptimalBAI_OptProportions_ExpFamily
import Definitions.Def_OptimalBAI_OptProportions_OptimalProportions
import Definitions.Def_OptimalBAI_TrackStop_ExpFamily
import Definitions.Def_OptimalBAI_TrackStop_Tracking
import Definitions.Def_bernoulliRelativeEntropy



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


open MeasureTheory InformationTheory
open scoped ENNReal
set_option maxHeartbeats 1500000
namespace OptimalBAI.LowerBound.ExpFamily

noncomputable def toTrackFamily (F : ExpFamily) : OptimalBAI.TrackStop.ExpFamily where
  ξ := F.ξ
  Θ := F.Θ
  b := F.b
  isOpen_Θ := F.isOpen_Θ
  ordConnected_Θ := F.ordConnected_Θ
  nonempty_Θ := F.nonempty_Θ
  isNormalized := F.isNormalized
  contDiff := F.contDiff
  deriv2_pos := F.deriv2_pos

lemma reward_integrable (F : ExpFamily) (θ : ℝ) (hθ : θ∈F.Θ) : Integrable id (F.arm θ) :=
  F.toTrackFamily.reward_integrable θ hθ

lemma mean_integral (F : ExpFamily) (θ : ℝ) (hθ : θ∈F.Θ) :
    (∫ x : ℝ,x ∂F.arm θ)=deriv F.b θ := F.toTrackFamily.mean_integral θ hθ

lemma relative_arm (F : ExpFamily) (θ φ : ℝ) :
    (F.arm φ).withDensity (fun x => ENNReal.ofReal
      (Real.exp ((θ-φ)*x-(F.b θ-F.b φ))))=F.arm θ := F.toTrackFamily.relative_arm θ φ

lemma arm_ac (F : ExpFamily) (θ φ : ℝ) : F.arm θ≪F.arm φ := F.toTrackFamily.arm_ac θ φ

lemma kl_parameter (F : ExpFamily) (θ φ : ℝ) (hθ : θ∈F.Θ) (hφ : φ∈F.Θ) :
    klDiv (F.arm θ) (F.arm φ)=ENNReal.ofReal (F.b φ-F.b θ-deriv F.b θ*(φ-θ)) :=
  F.toTrackFamily.kl_parameter θ φ hθ hφ

end OptimalBAI.LowerBound.ExpFamily


open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal
set_option maxHeartbeats 2000000
namespace OptimalBAI.LowerBound

noncomputable def oneLLR (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ) (z : Fin K × ℝ) : ℝ :=
  ((θ z.1 : ℝ)-(φ z.1 : ℝ))*z.2-(F.b (θ z.1)-F.b (φ z.1))

noncomputable def oneDensity (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ) (z : Fin K × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (oneLLR F θ φ z))

lemma oneLLR_measurable (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ) : Measurable (oneLLR F θ φ) := by
  unfold oneLLR
  have ht : Measurable (fun z : Fin K × ℝ => (θ z.1 : ℝ)) := (measurable_of_countable (fun a => (θ a : ℝ))).comp measurable_fst
  have hp : Measurable (fun z : Fin K × ℝ => (φ z.1 : ℝ)) := (measurable_of_countable (fun a => (φ a : ℝ))).comp measurable_fst
  have hbt : Measurable (fun z : Fin K × ℝ => F.b (θ z.1)) := (measurable_of_countable (fun a => F.b (θ a))).comp measurable_fst
  have hbp : Measurable (fun z : Fin K × ℝ => F.b (φ z.1)) := (measurable_of_countable (fun a => F.b (φ a))).comp measurable_fst
  exact ((ht.sub hp).mul measurable_snd).sub (hbt.sub hbp)

lemma oneDensity_measurable (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ) : Measurable (oneDensity F θ φ) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (oneLLR_measurable F θ φ))

noncomputable def histLLR (F : ExpFamily) {K n : ℕ} (θ φ : Fin K → F.Θ) (h : BanditHistory K n) : ℝ :=
  ∑ i,oneLLR F θ φ (h i)

noncomputable def histDensity (F : ExpFamily) {K n : ℕ} (θ φ : Fin K → F.Θ) (h : BanditHistory K n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (histLLR F θ φ h))

lemma histLLR_measurable (F : ExpFamily) {K n : ℕ} (θ φ : Fin K → F.Θ) : Measurable (histLLR (n := n) F θ φ) :=
  Finset.measurable_sum _ (fun i _ => (oneLLR_measurable F θ φ).comp (measurable_pi_apply i))

lemma histDensity_measurable (F : ExpFamily) {K n : ℕ} (θ φ : Fin K → F.Θ) : Measurable (histDensity (n := n) F θ φ) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (histLLR_measurable F θ φ))

lemma histLLR_snoc (F : ExpFamily) {K n : ℕ} (θ φ : Fin K → F.Θ) (h : BanditHistory K n) (z : Fin K × ℝ) :
    histLLR F θ φ (Fin.snoc h z)=histLLR F θ φ h+oneLLR F θ φ z := by
  unfold histLLR
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]

lemma histDensity_snoc (F : ExpFamily) {K n : ℕ} (θ φ : Fin K → F.Θ) (h : BanditHistory K n) (z : Fin K × ℝ) :
    histDensity F θ φ (Fin.snoc h z)=histDensity F θ φ h*oneDensity F θ φ z := by
  unfold histDensity
  rw [histLLR_snoc,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
  rfl

lemma step_density (F : ExpFamily) {K n : ℕ} (θ φ : Fin K → F.Θ) (π : BanditPolicy K)
    (h : BanditHistory K n) (f : Fin K × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z,f z ∂banditStepKernel (expFamilyBandit F θ) π n h)=
      ∫⁻ z,oneDensity F θ φ z*f z ∂banditStepKernel (expFamilyBandit F φ) π n h := by
  change (∫⁻ z,f z ∂banditStepKernel (expFamilyBandit F θ) π n h)=
    ∫⁻ z,(oneDensity F θ φ*f) z ∂banditStepKernel (expFamilyBandit F φ) π n h
  rw [banditStepKernel,Kernel.lintegral_compProd _ _ _ hf,
    banditStepKernel,Kernel.lintegral_compProd _ _ _ ((oneDensity_measurable F θ φ).mul hf)]
  simp only [Kernel.comap_apply]
  change (∫⁻ a, ∫⁻ x,f (a,x) ∂F.arm (θ a) ∂π.select n h)=
    ∫⁻ a, ∫⁻ x,oneDensity F θ φ (a,x)*f (a,x) ∂F.arm (φ a) ∂π.select n h
  apply lintegral_congr
  intro a
  rw [←F.relative_arm (θ a) (φ a),lintegral_withDensity_eq_lintegral_mul]
  · rfl
  · fun_prop
  · exact hf.comp measurable_prodMk_left

end OptimalBAI.LowerBound


open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal
set_option maxHeartbeats 2000000
namespace OptimalBAI.LowerBound

noncomputable def informationCost (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ) (a : Fin K) : ℝ :=
  F.b (φ a)-F.b (θ a)-deriv F.b (θ a)*((φ a : ℝ)-(θ a : ℝ))

lemma oneLLR_integrable (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ) (a : Fin K) :
    Integrable (fun x => oneLLR F θ φ (a,x)) (F.arm (θ a)) := by
  letI := F.isProbabilityMeasure_arm (θ a).2
  change Integrable (fun x => ((θ a : ℝ)-(φ a : ℝ))*x-(F.b (θ a)-F.b (φ a))) (F.arm (θ a))
  exact ((F.reward_integrable (θ a) (θ a).2).const_mul ((θ a : ℝ)-(φ a : ℝ))).sub
    (integrable_const (F.b (θ a)-F.b (φ a)))

lemma oneLLR_mean (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ) (a : Fin K) :
    (∫ x,oneLLR F θ φ (a,x) ∂F.arm (θ a))=informationCost F θ φ a := by
  letI := F.isProbabilityMeasure_arm (θ a).2
  change (∫ x,((θ a : ℝ)-(φ a : ℝ))*x-(F.b (θ a)-F.b (φ a)) ∂F.arm (θ a))=_
  have hl : Integrable (fun x : ℝ => ((θ a : ℝ)-(φ a : ℝ))*x) (F.arm (θ a)) :=
    (F.reward_integrable (θ a) (θ a).2).const_mul _
  rw [integral_sub hl (integrable_const (F.b (θ a)-F.b (φ a))),
    integral_const_mul,F.mean_integral (θ a) (θ a).2]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  unfold informationCost
  ring

lemma informationCost_pos (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ) (a : Fin K)
    (hne : θ a≠φ a) : 0 < informationCost F θ φ a := by
  let G := F.toTrackFamily.toAllocationFamily
  have hp : (θ a : ℝ)≠(φ a : ℝ) := fun h => hne (Subtype.ext h)
  rcases lt_or_gt_of_ne hp with hlt | hgt
  · have hs := G.b_strictConvex.lt_slope_of_hasDerivAt
      (θ a).2 (φ a).2 hlt (G.b_differentiableAt (θ a).2).hasDerivAt
    rw [slope_def_field] at hs
    have hh := (lt_div_iff₀ (sub_pos.mpr hlt)).mp hs
    change deriv F.b (θ a)*((φ a : ℝ)-(θ a : ℝ))<F.b (φ a)-F.b (θ a) at hh
    dsimp [informationCost]
    linarith
  · have hs := G.b_strictConvex.slope_lt_of_hasDerivAt
      (φ a).2 (θ a).2 hgt (G.b_differentiableAt (θ a).2).hasDerivAt
    rw [slope_def_field] at hs
    have hh := (div_lt_iff₀ (sub_pos.mpr hgt)).mp hs
    change F.b (θ a)-F.b (φ a)<deriv F.b (θ a)*((θ a : ℝ)-(φ a : ℝ)) at hh
    dsimp [informationCost]
    linarith

lemma informationCost_nonneg (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ) (a : Fin K) :
    0 ≤ informationCost F θ φ a := by
  by_cases h : θ a=φ a
  · simp [informationCost,h]
  · exact (informationCost_pos F θ φ a h).le

lemma kl_cost (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ) (a : Fin K) :
    klDiv (F.arm (θ a)) (F.arm (φ a))=ENNReal.ofReal (informationCost F θ φ a) :=
  F.kl_parameter _ _ (θ a).2 (φ a).2

end OptimalBAI.LowerBound


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


open MeasureTheory ProbabilityTheory BanditAlgorithm Preorder
open scoped ENNReal
set_option maxHeartbeats 2000000
namespace OptimalBAI.LowerBound

lemma trajectory_prefix_integral {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) :
    ∀ n : ℕ, ∀ f : BanditHistory K n → ℝ≥0∞, Measurable f →
      (∫⁻ ω,f (banditTrajPrefix K n ω) ∂banditTrajMeasure ν π)=∫⁻ h,f h ∂banditMeasure ν π n := by
  let P := banditTrajMeasure ν π
  let μ₀ := banditStepKernel ν π 0 (fun i => i.elim0)
  let κ := banditTrajKernel ν π
  intro n
  induction n with
  | zero =>
    intro f hf
    have he (ω : ℕ → Fin K × ℝ) : banditTrajPrefix K 0 ω=(fun i => i.elim0) := Subsingleton.elim _ _
    simp_rw [he]
    simp [banditMeasure]
  | succ n ih =>
    cases n with
    | zero =>
      intro f hf
      let f₀ := fun h : Finset.Iic 0 → Fin K × ℝ => f (banditIicHistory K 0 h)
      have hm : Measurable f₀ := hf.comp measurable_banditIicHistory
      change (∫⁻ ω,f₀ (frestrictLe 0 ω) ∂P)=_
      rw [←lintegral_map hm (measurable_frestrictLe 0)]
      have hmap : P.map (frestrictLe 0)=μ₀.map
          (MeasurableEquiv.piUnique (fun _i : Finset.Iic 0 => Fin K × ℝ)).symm :=
        OptimalBAI.TrackStop.initial_prefix_law μ₀ κ
      rw [hmap,lintegral_map hm (MeasurableEquiv.piUnique _).symm.measurable]
      have heq (z : Fin K × ℝ) : f₀ ((MeasurableEquiv.piUnique _).symm z)=
          f (Fin.snoc (fun i : Fin 0 => i.elim0) z) := by
        apply congrArg f
        funext i
        have hi : i=0 := Fin.eq_zero i
        subst i
        rfl
      simp_rw [heq]
      have hsn : Measurable (fun p : BanditHistory K 0 × (Fin K × ℝ) => f (Fin.snoc p.1 p.2)) :=
        hf.comp measurable_banditHistorySnoc
      conv_rhs => rw [banditMeasure,lintegral_map hf measurable_banditHistorySnoc,
        Measure.lintegral_compProd hsn]
      simp only [banditMeasure,lintegral_dirac]
      rfl
    | succ t =>
      intro f hf
      let g := fun h : BanditHistory K (t+1) => ∫⁻ z,f (Fin.snoc h z) ∂banditStepKernel ν π (t+1) h
      have hgm : Measurable g := (hf.comp measurable_banditHistorySnoc).lintegral_kernel_prod_right'
      let Q := P.map (frestrictLe t)
      have hjoint : Q⊗ₘκ t=P.map (fun ω => (frestrictLe t ω,ω (t+1))) :=
        Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      have hm : Measurable (fun p : (Finset.Iic t → Fin K × ℝ) × (Fin K × ℝ) =>
          f (Fin.snoc (banditIicHistory K t p.1) p.2)) :=
        hf.comp (measurable_banditHistorySnoc.comp
          ((measurable_banditIicHistory.comp measurable_fst).prodMk measurable_snd))
      calc
        _=∫⁻ p,f (Fin.snoc (banditIicHistory K t p.1) p.2)
            ∂P.map (fun ω => (frestrictLe t ω,ω (t+1))) := by
          rw [lintegral_map hm (by fun_prop)]
          apply lintegral_congr
          intro ω
          rw [←OptimalBAI.TrackStop.iicHistory_snoc,OptimalBAI.TrackStop.iicHistory_prefix]
        _=∫⁻ p,f (Fin.snoc (banditIicHistory K t p.1) p.2) ∂(Q⊗ₘκ t) := by rw [hjoint]
        _=∫⁻ h,g (banditIicHistory K t h) ∂Q := by
          rw [Measure.lintegral_compProd hm]
          rfl
        _=∫⁻ ω,g (banditTrajPrefix K (t+1) ω) ∂P := by
          dsimp only [Q]
          rw [lintegral_map (show Measurable (fun h => g (banditIicHistory K t h)) from
            hgm.comp measurable_banditIicHistory) (measurable_frestrictLe t)]
          rfl
        _=∫⁻ h,g h ∂banditMeasure ν π (t+1) := ih g hgm
        _=∫⁻ h,f h ∂banditMeasure ν π (t+1+1) := by
          have hsn : Measurable (fun p : BanditHistory K (t+1) × (Fin K × ℝ) => f (Fin.snoc p.1 p.2)) :=
            hf.comp measurable_banditHistorySnoc
          conv_rhs => rw [banditMeasure,lintegral_map hf measurable_banditHistorySnoc,
            Measure.lintegral_compProd hsn]

end OptimalBAI.LowerBound


open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal
set_option maxHeartbeats 2000000
namespace OptimalBAI.LowerBound

lemma trajectory_step_lintegral {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K)
    (n : ℕ) (f : BanditHistory K n × (Fin K × ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω,f (banditTrajPrefix K n ω,ω n) ∂banditTrajMeasure ν π)=
      ∫⁻ ω,∫⁻ z,f (banditTrajPrefix K n ω,z) ∂banditStepKernel ν π n (banditTrajPrefix K n ω)
        ∂banditTrajMeasure ν π := by
  let g := fun h : BanditHistory K (n+1) => f ((fun i => h i.castSucc),h (Fin.last n))
  have hg : Measurable g := hf.comp (by fun_prop)
  have hsn : Measurable (fun p : BanditHistory K n × (Fin K × ℝ) => g (Fin.snoc p.1 p.2)) :=
    hg.comp measurable_banditHistorySnoc
  have hi : Measurable (fun h : BanditHistory K n => ∫⁻ z,f (h,z) ∂banditStepKernel ν π n h) :=
    hf.lintegral_kernel_prod_right'
  calc
    _=∫⁻ ω,g (banditTrajPrefix K (n+1) ω) ∂banditTrajMeasure ν π := rfl
    _=∫⁻ h,g h ∂banditMeasure ν π (n+1) := trajectory_prefix_integral ν π (n+1) g hg
    _=∫⁻ h,∫⁻ z,f (h,z) ∂banditStepKernel ν π n h ∂banditMeasure ν π n := by
      rw [banditMeasure,lintegral_map hg measurable_banditHistorySnoc,Measure.lintegral_compProd hsn]
      simp only [g,Fin.snoc_castSucc,Fin.snoc_last]
    _=_ := (trajectory_prefix_integral ν π n _ hi).symm

lemma adapted_step_lintegral {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K)
    (n : ℕ) (A : Set (ℕ → Fin K × ℝ)) (hA : MeasurableSet[banditFiltration K n] A)
    (g : Fin K × ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω,A.indicator (fun ω => g (ω n)) ω ∂banditTrajMeasure ν π)=
      ∫⁻ ω,A.indicator (fun ω => ∫⁻ z,g z ∂banditStepKernel ν π n (banditTrajPrefix K n ω)) ω
        ∂banditTrajMeasure ν π := by
  classical
  obtain ⟨B,hB,hpre⟩ := hA
  let f := fun p : BanditHistory K n × (Fin K × ℝ) => B.indicator (fun _ => g p.2) p.1
  have hf : Measurable f := (hg.comp measurable_snd).indicator (hB.preimage measurable_fst)
  have ht := trajectory_step_lintegral ν π n f hf
  rw [←hpre]
  calc
    _=∫⁻ ω,f (banditTrajPrefix K n ω,ω n) ∂banditTrajMeasure ν π := rfl
    _=_ := ht
    _=_ := by
      apply lintegral_congr
      intro ω
      by_cases h : banditTrajPrefix K n ω∈B
      · simp [f,Set.indicator,h]
      · simp [f,Set.indicator,h]

lemma step_reward_integral {K n : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K)
    (h : BanditHistory K n) (g : Fin K × ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z,g z ∂banditStepKernel ν π n h)=
      ∑ a : Fin K,(π.select n h) {a}*(∫⁻ x,g (a,x) ∂ν.P a) := by
  rw [banditStepKernel,Kernel.lintegral_compProd _ _ _ hg]
  simp only [Kernel.comap_apply]
  rw [lintegral_fintype]
  apply Finset.sum_congr rfl
  intro a ha
  exact mul_comm _ _

end OptimalBAI.LowerBound


open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal
set_option maxHeartbeats 2000000
namespace OptimalBAI.LowerBound

lemma adapted_arm_probability {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K)
    (n : ℕ) (A : Set (ℕ → Fin K × ℝ)) (hA : MeasurableSet[banditFiltration K n] A)
    (a : Fin K) :
    banditTrajMeasure ν π (A∩{ω | (ω n).1=a})=
      ∫⁻ ω,A.indicator (fun ω => (π.select n (banditTrajPrefix K n ω)) {a}) ω
        ∂banditTrajMeasure ν π := by
  classical
  let g := fun z : Fin K × ℝ => if z.1=a then (1 : ℝ≥0∞) else 0
  have hg : Measurable g := measurable_const.ite
    (measurableSet_eq_fun measurable_fst measurable_const) measurable_const
  have ht := adapted_step_lintegral ν π n A hA g hg
  have hstep (h : BanditHistory K n) : (∫⁻ z,g z ∂banditStepKernel ν π n h)=(π.select n h) {a} := by
    rw [step_reward_integral ν π h g hg]
    have heq (b : Fin K) : (∫⁻ x,g (b,x) ∂ν.P b)=if b=a then 1 else 0 := by
      letI := ν.prob b
      by_cases hb : b=a <;> simp [g,hb]
    simp_rw [heq]
    simp
  have hAg : MeasurableSet A := (banditFiltration K).le n _ hA
  have hAn : MeasurableSet (A∩{ω | (ω n).1=a}) := hAg.inter ((measurableSet_singleton a).preimage (show Measurable (fun ω : ℕ → Fin K × ℝ => (ω n).1) from
    measurable_fst.comp (measurable_pi_apply n)))
  rw [←lintegral_indicator_one hAn]
  calc
    _=∫⁻ ω,A.indicator (fun ω => g (ω n)) ω ∂banditTrajMeasure ν π := by
      apply lintegral_congr
      intro ω
      by_cases h : ω∈A <;> by_cases ha : (ω n).1=a <;> simp [Set.indicator,g,h,ha]
    _=_ := ht
    _=_ := by simp_rw [hstep]

lemma adapted_reward_occupation {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K)
    (n : ℕ) (A : Set (ℕ → Fin K × ℝ)) (hA : MeasurableSet[banditFiltration K n] A)
    (g : Fin K × ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω,A.indicator (fun ω => g (ω n)) ω ∂banditTrajMeasure ν π)=
      ∑ a : Fin K,(∫⁻ x,g (a,x) ∂ν.P a)*banditTrajMeasure ν π (A∩{ω | (ω n).1=a}) := by
  classical
  rw [adapted_step_lintegral ν π n A hA g hg]
  simp_rw [step_reward_integral ν π _ g hg]
  have hAg : MeasurableSet A := (banditFiltration K).le n _ hA
  have heq (ω : ℕ → Fin K × ℝ) :
      A.indicator (fun ω => ∑ a : Fin K,(π.select n (banditTrajPrefix K n ω)) {a}*
        (∫⁻ x,g (a,x) ∂ν.P a)) ω=
      ∑ a : Fin K,(∫⁻ x,g (a,x) ∂ν.P a)*
        A.indicator (fun ω => (π.select n (banditTrajPrefix K n ω)) {a}) ω := by
    by_cases hw : ω∈A
    · simp only [Set.indicator_of_mem hw]
      apply Finset.sum_congr rfl
      intro a ha
      exact mul_comm _ _
    · simp [Set.indicator_of_notMem hw]
  simp_rw [heq]
  have hm (a : Fin K) : Measurable (fun ω => (π.select n (banditTrajPrefix K n ω)) {a}) :=
    ((π.select n).measurable_coe (measurableSet_singleton a)).comp measurable_banditTrajPrefix
  rw [lintegral_finsetSum _ (fun a _ =>
    (show Measurable (fun ω => (∫⁻ x,g (a,x) ∂ν.P a)*
      A.indicator (fun ω => (π.select n (banditTrajPrefix K n ω)) {a}) ω) from
      measurable_const.mul ((hm a).indicator hAg)))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [lintegral_const_mul _ ((hm a).indicator hAg),←adapted_arm_probability ν π n A hA a]

noncomputable def stoppedReward {K : ℕ} (τ : (ℕ → Fin K × ℝ) → ℕ∞)
    (g : Fin K × ℝ → ℝ≥0∞) (ω : ℕ → Fin K × ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ,{ω | (n : ℕ∞)<τ ω}.indicator (fun ω => g (ω n)) ω

lemma stopped_reward_occupation {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K)
    {τ : (ℕ → Fin K × ℝ) → ℕ∞} (hτ : IsBanditStoppingTime τ)
    (g : Fin K × ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω,stoppedReward τ g ω ∂banditTrajMeasure ν π)=
      ∑ a : Fin K,(∫⁻ x,g (a,x) ∂ν.P a)*
        ∑' n : ℕ,banditTrajMeasure ν π {ω | (n : ℕ∞)<τ ω ∧ (ω n).1=a} := by
  have hAn (n : ℕ) : MeasurableSet[banditFiltration K n] {ω | (n : ℕ∞)<τ ω} := by
    have h : MeasurableSet[banditFiltration K n] {ω | τ ω≤(n : ℕ∞)} := hτ n
    have heq : {ω | (n : ℕ∞)<τ ω}={ω | τ ω≤(n : ℕ∞)}ᶜ := by
      ext ω
      change (n : ℕ∞)<τ ω ↔ ¬τ ω≤(n : ℕ∞)
      exact lt_iff_not_ge
    rw [heq]
    exact h.compl
  have hAg (n : ℕ) : MeasurableSet {ω | (n : ℕ∞)<τ ω} := (banditFiltration K).le n _ (hAn n)
  unfold stoppedReward
  rw [lintegral_tsum (fun (n : ℕ) => (show Measurable ({ω | (n : ℕ∞)<τ ω}.indicator
    (fun ω => g (ω n))) from ((hg.comp (measurable_pi_apply n)).indicator (hAg n))).aemeasurable)]
  simp_rw [adapted_reward_occupation ν π _ _ (hAn _) g hg]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [←ENNReal.tsum_mul_left]
  rfl

end OptimalBAI.LowerBound


open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal
set_option maxHeartbeats 2000000
namespace OptimalBAI.LowerBound

lemma stopped_count_series {K : ℕ} (a : Fin K)
    {τ : (ℕ → Fin K × ℝ) → ℕ∞} {ω : ℕ → Fin K × ℝ} (hfin : τ ω≠⊤) :
    (trajPullCount a (τ ω).toNat ω : ℝ≥0∞)=
      ∑' n : ℕ,if (n : ℕ∞)<τ ω ∧ (ω n).1=a then (1 : ℝ≥0∞) else 0 := by
  classical
  have ht : ((τ ω).toNat : ℕ∞)=τ ω := ENat.natCast_toNat hfin
  rw [←ht]
  simp only [ENat.toNat_coe,ENat.coe_lt_coe]
  rw [tsum_eq_sum (s := Finset.range (τ ω).toNat)]
  · unfold trajPullCount
    rw [Finset.card_eq_sum_ones,Finset.sum_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_range] at hn
    simp [hn]
  · intro n hn
    simp only [Finset.mem_range,not_lt] at hn
    simp [not_lt.mpr hn]

lemma expected_count_series {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K)
    {τ : (ℕ → Fin K × ℝ) → ℕ∞} (hτ : IsBanditStoppingTime τ)
    (hfin : ∀ᵐ ω ∂banditTrajMeasure ν π,τ ω≠⊤) (a : Fin K) :
    (∫⁻ ω,(trajPullCount a (τ ω).toNat ω : ℝ≥0∞) ∂banditTrajMeasure ν π)=
      ∑' n : ℕ,banditTrajMeasure ν π {ω | (n : ℕ∞)<τ ω ∧ (ω n).1=a} := by
  classical
  have hAn (n : ℕ) : MeasurableSet {ω | (n : ℕ∞)<τ ω ∧ (ω n).1=a} := by
    have hlev : MeasurableSet {ω | (n : ℕ∞)<τ ω} :=
      (banditFiltration K).le n _ (by
        have h : MeasurableSet[banditFiltration K n] {ω | τ ω≤(n : ℕ∞)} := hτ n
        have heq : {ω | (n : ℕ∞)<τ ω}={ω | τ ω≤(n : ℕ∞)}ᶜ := by
          ext ω
          change (n : ℕ∞)<τ ω ↔ ¬τ ω≤(n : ℕ∞)
          exact lt_iff_not_ge
        rw [heq]
        exact h.compl)
    exact hlev.inter ((measurableSet_singleton a).preimage (show Measurable (fun ω : ℕ → Fin K × ℝ => (ω n).1) from
      measurable_fst.comp (measurable_pi_apply n)))
  have heq : (fun ω => (trajPullCount a (τ ω).toNat ω : ℝ≥0∞))=ᵐ[banditTrajMeasure ν π]
      fun ω => ∑' n : ℕ,({ω | (n : ℕ∞)<τ ω ∧ (ω n).1=a}.indicator (fun _ => (1 : ℝ≥0∞))) ω := by
    filter_upwards [hfin] with ω hω
    simpa only [Set.indicator,Set.mem_setOf_eq] using stopped_count_series a hω
  rw [lintegral_congr_ae heq,lintegral_tsum (fun n => (measurable_const.indicator (hAn n)).aemeasurable)]
  apply tsum_congr
  intro n
  exact lintegral_indicator_one (hAn n)

lemma stopped_reward_counts {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K)
    {τ : (ℕ → Fin K × ℝ) → ℕ∞} (hτ : IsBanditStoppingTime τ)
    (hfin : ∀ᵐ ω ∂banditTrajMeasure ν π,τ ω≠⊤)
    (g : Fin K × ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω,stoppedReward τ g ω ∂banditTrajMeasure ν π)=
      ∑ a : Fin K,(∫⁻ x,g (a,x) ∂ν.P a)*
        ∫⁻ ω,(trajPullCount a (τ ω).toNat ω : ℝ≥0∞) ∂banditTrajMeasure ν π := by
  rw [stopped_reward_occupation ν π hτ g hg]
  simp_rw [expected_count_series ν π hτ hfin]

end OptimalBAI.LowerBound


open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal
set_option maxHeartbeats 2000000
namespace OptimalBAI.LowerBound

lemma finite_density (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ) (π : BanditPolicy K) :
    ∀ n : ℕ, ∀ f : BanditHistory K n → ℝ≥0∞, Measurable f →
      (∫⁻ h,f h ∂banditMeasure (expFamilyBandit F θ) π n)=
        ∫⁻ h,histDensity F θ φ h*f h ∂banditMeasure (expFamilyBandit F φ) π n := by
  intro n
  induction n with
  | zero =>
    intro f hf
    simp [banditMeasure,histDensity,histLLR]
  | succ n ih =>
    intro f hf
    let g := fun h : BanditHistory K n =>
      ∫⁻ z,f (Fin.snoc h z) ∂banditStepKernel (expFamilyBandit F θ) π n h
    have hm : Measurable (fun p : BanditHistory K n × (Fin K × ℝ) => f (Fin.snoc p.1 p.2)) :=
      hf.comp measurable_banditHistorySnoc
    have hg : Measurable g := hm.lintegral_kernel_prod_right'
    rw [banditMeasure,lintegral_map hf measurable_banditHistorySnoc,Measure.lintegral_compProd hm,
      ih g hg]
    change (∫⁻ h,histDensity F θ φ h*g h ∂banditMeasure (expFamilyBandit F φ) π n)=_
    change (∫⁻ h,histDensity F θ φ h*g h ∂banditMeasure (expFamilyBandit F φ) π n)=
      ∫⁻ h,(histDensity (n := n+1) F θ φ*f) h ∂banditMeasure (expFamilyBandit F φ) π (n+1)
    rw [banditMeasure,lintegral_map ((histDensity_measurable F θ φ).mul hf) measurable_banditHistorySnoc,
      Measure.lintegral_compProd (show Measurable (fun p : BanditHistory K n × (Fin K × ℝ) =>
        (histDensity (n := n+1) F θ φ*f) (Fin.snoc p.1 p.2)) from
        (((histDensity_measurable F θ φ).mul hf).comp measurable_banditHistorySnoc))]
    apply lintegral_congr
    intro h
    dsimp [g]
    rw [step_density F θ φ π h (fun z => f (Fin.snoc h z)) (hf.comp (measurable_banditHistorySnoc.comp measurable_prodMk_left))]
    simp_rw [histDensity_snoc,mul_assoc]
    rw [lintegral_const_mul _ (show Measurable (fun z => oneDensity F θ φ z*f (Fin.snoc h z)) from
      ((oneDensity_measurable F θ φ).mul
      (hf.comp (measurable_banditHistorySnoc.comp measurable_prodMk_left))))]

end OptimalBAI.LowerBound


open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal
set_option maxHeartbeats 2000000
namespace OptimalBAI.LowerBound

lemma prefix_density (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ) (π : BanditPolicy K)
    (n : ℕ) (f : BanditHistory K n → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω,f (banditTrajPrefix K n ω) ∂banditTrajMeasure (expFamilyBandit F θ) π)=
      ∫⁻ ω,histDensity F θ φ (banditTrajPrefix K n ω)*f (banditTrajPrefix K n ω)
        ∂banditTrajMeasure (expFamilyBandit F φ) π := by
  rw [trajectory_prefix_integral _ _ n f hf,finite_density F θ φ π n f hf]
  exact (trajectory_prefix_integral _ _ n (fun h => histDensity F θ φ h*f h)
    ((histDensity_measurable F θ φ).mul hf)).symm

lemma prefix_event_density (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ) (π : BanditPolicy K)
    (n : ℕ) (A : Set (ℕ → Fin K × ℝ)) (hA : MeasurableSet[banditFiltration K n] A) :
    banditTrajMeasure (expFamilyBandit F θ) π A=
      ∫⁻ ω,A.indicator (fun ω => histDensity F θ φ (banditTrajPrefix K n ω)) ω
        ∂banditTrajMeasure (expFamilyBandit F φ) π := by
  classical
  obtain ⟨B,hB,hpre⟩ := hA
  have hi : Measurable (B.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hB
  have h := prefix_density F θ φ π n _ hi
  rw [←hpre]
  calc
    _=∫⁻ ω,B.indicator (fun _ => (1 : ℝ≥0∞)) (banditTrajPrefix K n ω)
        ∂banditTrajMeasure (expFamilyBandit F θ) π := by
      rw [←lintegral_indicator_one (hB.preimage measurable_banditTrajPrefix)]
      apply lintegral_congr
      intro ω
      by_cases hw : banditTrajPrefix K n ω∈B <;> simp [Set.indicator,hw]
    _=_ := h
    _=_ := by
      apply lintegral_congr
      intro ω
      by_cases hw : banditTrajPrefix K n ω∈B <;> simp [Set.indicator,hw]

end OptimalBAI.LowerBound


open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal
set_option maxHeartbeats 2000000
namespace OptimalBAI.LowerBound

noncomputable def stoppedLLR (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ)
    (τ : (ℕ → Fin K × ℝ) → ℕ∞) : (ℕ → Fin K × ℝ) → ℝ :=
  stoppedValue (fun n ω => histLLR F θ φ (banditTrajPrefix K n ω)) τ

noncomputable def stoppedDensity (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ)
    (τ : (ℕ → Fin K × ℝ) → ℕ∞) (ω : ℕ → Fin K × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (stoppedLLR F θ φ τ ω))

lemma stoppedLLR_measurable (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ)
    {τ : (ℕ → Fin K × ℝ) → ℕ∞} (hτ : IsBanditStoppingTime τ) :
    Measurable[hτ.measurableSpace] (stoppedLLR F θ φ τ) := by
  have ha : StronglyAdapted (banditFiltration K)
      (fun n ω => histLLR F θ φ (banditTrajPrefix K n ω)) := by
    intro n
    exact ((histLLR_measurable F θ φ).comp (comap_measurable _)).stronglyMeasurable
  exact measurable_stoppedValue ha.isStronglyProgressive_of_discrete hτ

lemma stoppedDensity_measurable (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ)
    {τ : (ℕ → Fin K × ℝ) → ℕ∞} (hτ : IsBanditStoppingTime τ) :
    Measurable[hτ.measurableSpace] (stoppedDensity F θ φ τ) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (stoppedLLR_measurable F θ φ hτ))

lemma stoppedDensity_eq (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ)
    {τ : (ℕ → Fin K × ℝ) → ℕ∞} {ω : ℕ → Fin K × ℝ} {n : ℕ} (h : τ ω=n) :
    stoppedDensity F θ φ τ ω=histDensity F θ φ (banditTrajPrefix K n ω) := by
  change (τ ω : WithTop ℕ)= (n : WithTop ℕ) at h
  unfold stoppedDensity stoppedLLR stoppedValue histDensity
  rw [h]
  rfl

lemma finite_stopping_partition {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (τ : Ω → ℕ∞) (hτ : ∀ n : ℕ,MeasurableSet {ω | τ ω=(n : ℕ∞)}) (hfin : ∀ᵐ ω ∂P,τ ω≠⊤)
    (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω,f ω ∂P)=∑' n : ℕ,∫⁻ ω,{ω | τ ω=(n : ℕ∞)}.indicator f ω ∂P := by
  classical
  have heq : f=ᵐ[P] fun ω => ∑' n : ℕ,{ω | τ ω=(n : ℕ∞)}.indicator f ω := by
    filter_upwards [hfin] with ω hω
    obtain ⟨n,hn⟩ := ENat.ne_top_iff_exists.mp hω
    have hsingle : (∑' j : ℕ,{ω | τ ω=(j : ℕ∞)}.indicator f ω)=
        {ω | τ ω=(n : ℕ∞)}.indicator f ω := by
      apply tsum_eq_single n
      intro j hj
      have hne : τ ω≠(j : ℕ∞) := by rw [←hn]; exact_mod_cast Ne.symm hj
      simp [Set.indicator,hne]
    rw [hsingle]
    simp [Set.indicator,hn.symm]
  rw [lintegral_congr_ae heq,lintegral_tsum]
  intro n
  exact (hf.indicator (hτ n)).aemeasurable

lemma stopped_event_density (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ) (π : BanditPolicy K)
    {τ : (ℕ → Fin K × ℝ) → ℕ∞} (hτ : IsBanditStoppingTime τ)
    (hθ : ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F θ) π,τ ω≠⊤)
    (hφ : ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F φ) π,τ ω≠⊤)
    (A : Set (ℕ → Fin K × ℝ)) (hA : MeasurableSet[hτ.measurableSpace] A) :
    banditTrajMeasure (expFamilyBandit F θ) π A=
      ∫⁻ ω,A.indicator (stoppedDensity F θ φ τ) ω ∂banditTrajMeasure (expFamilyBandit F φ) π := by
  classical
  have hAg : MeasurableSet A := hτ.measurableSpace_le _ hA
  have hR : Measurable (stoppedDensity F θ φ τ) :=
    (stoppedDensity_measurable F θ φ hτ).mono hτ.measurableSpace_le le_rfl
  have hlevels (n : ℕ) : MeasurableSet {ω | τ ω=(n : ℕ∞)} :=
    (banditFiltration K).le n _ (hτ.measurableSet_eq n)
  rw [←lintegral_indicator_one hAg,
    finite_stopping_partition _ τ hlevels hθ (A.indicator (1 : (ℕ → Fin K × ℝ) → ℝ≥0∞))
      (show Measurable (A.indicator (1 : (ℕ → Fin K × ℝ) → ℝ≥0∞)) from measurable_const.indicator hAg),
    finite_stopping_partition _ τ hlevels hφ _ (hR.indicator hAg)]
  apply tsum_congr
  intro n
  have hAn : MeasurableSet[banditFiltration K n] (A∩{ω | τ ω=(n : ℕ∞)}) :=
    (hτ.measurableSet_inter_eq_iff A n).mp
      (hA.inter (hτ.measurableSet_eq' n))
  have hAng : MeasurableSet (A∩{ω | τ ω=(n : ℕ∞)}) := (banditFiltration K).le n _ hAn
  simp_rw [Set.indicator_indicator,Set.inter_comm {ω | τ ω=(n : ℕ∞)} A]
  rw [lintegral_indicator_one hAng,prefix_event_density F θ φ π n _ hAn]
  apply lintegral_congr
  intro ω
  by_cases h : ω∈A∩{ω | τ ω=(n : ℕ∞)}
  · simp only [Set.indicator_of_mem h]
    exact (stoppedDensity_eq F θ φ h.2).symm
  · simp only [Set.indicator_of_notMem h]

end OptimalBAI.LowerBound


open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal
set_option maxHeartbeats 2000000
namespace OptimalBAI.LowerBound

lemma stoppedReward_finite {K : ℕ} (τ : (ℕ → Fin K × ℝ) → ℕ∞)
    (g : Fin K × ℝ → ℝ≥0∞) (ω : ℕ → Fin K × ℝ) (hfin : τ ω≠⊤) :
    stoppedReward τ g ω=∑ n ∈ Finset.range (τ ω).toNat,g (ω n) := by
  classical
  have ht : ((τ ω).toNat : ℕ∞)=τ ω := ENat.natCast_toNat hfin
  unfold stoppedReward
  rw [tsum_eq_sum (s := Finset.range (τ ω).toNat)]
  · apply Finset.sum_congr rfl
    intro n hn
    have hn' : (n : ℕ∞)<τ ω := by rw [←ht]; exact_mod_cast Finset.mem_range.mp hn
    simp [Set.indicator,hn']
  · intro n hn
    have hn' : ¬(n : ℕ∞)<τ ω := by rw [←ht]; exact_mod_cast (show ¬n<(τ ω).toNat from fun h => hn (Finset.mem_range.mpr h))
    simp [Set.indicator,hn']

lemma stoppedLLR_parts (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ)
    (τ : (ℕ → Fin K × ℝ) → ℕ∞) (ω : ℕ → Fin K × ℝ) (hfin : τ ω≠⊤) :
    stoppedLLR F θ φ τ ω=
      (stoppedReward τ (fun z => ENNReal.ofReal (oneLLR F θ φ z)) ω).toReal-
      (stoppedReward τ (fun z => ENNReal.ofReal (-oneLLR F θ φ z)) ω).toReal := by
  classical
  have ht : (τ ω : WithTop ℕ)=((τ ω).toNat : WithTop ℕ) := (ENat.natCast_toNat hfin).symm
  unfold stoppedLLR stoppedValue
  rw [ht]
  change histLLR F θ φ (banditTrajPrefix K (τ ω).toNat ω)=_
  rw [stoppedReward_finite τ _ ω hfin,stoppedReward_finite τ _ ω hfin,
    ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top),
    ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top),←Finset.sum_sub_distrib]
  unfold histLLR banditTrajPrefix
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => oneLLR F θ φ (ω n)) (τ ω).toNat]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [ENNReal.toReal_ofReal']
  exact (max_zero_sub_max_neg_zero_eq_self _).symm

end OptimalBAI.LowerBound


open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal
set_option maxHeartbeats 2000000
namespace OptimalBAI.LowerBound

lemma stopped_llr_integral (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ) (π : BanditPolicy K)
    {τ : (ℕ → Fin K × ℝ) → ℕ∞} (hτ : IsBanditStoppingTime τ)
    (hfin : ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F θ) π,τ ω≠⊤)
    (htotal : (∑ a : Fin K,klDiv (F.arm (θ a)) (F.arm (φ a))*
      ∫⁻ ω,(trajPullCount a (τ ω).toNat ω : ℝ≥0∞) ∂banditTrajMeasure (expFamilyBandit F θ) π)≠⊤) :
    Integrable (stoppedLLR F θ φ τ) (banditTrajMeasure (expFamilyBandit F θ) π) ∧
      (∫ ω,stoppedLLR F θ φ τ ω ∂banditTrajMeasure (expFamilyBandit F θ) π)=
        (∑ a : Fin K,klDiv (F.arm (θ a)) (F.arm (φ a))*
          ∫⁻ ω,(trajPullCount a (τ ω).toNat ω : ℝ≥0∞) ∂banditTrajMeasure (expFamilyBandit F θ) π).toReal := by
  classical
  let ν := expFamilyBandit F θ
  let P := banditTrajMeasure ν π
  let N := fun a : Fin K => ∫⁻ ω,(trajPullCount a (τ ω).toNat ω : ℝ≥0∞) ∂P
  let gp := fun z => ENNReal.ofReal (oneLLR F θ φ z)
  let gm := fun z => ENNReal.ofReal (-oneLLR F θ φ z)
  let mp := fun a : Fin K => ∫⁻ x,gp (a,x) ∂F.arm (θ a)
  let mm := fun a : Fin K => ∫⁻ x,gm (a,x) ∂F.arm (θ a)
  have hprod (a : Fin K) : klDiv (F.arm (θ a)) (F.arm (φ a))*N a≠⊤ :=
    ne_of_lt ((Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ a)).trans_lt htotal.lt_top)
  have hn (a : Fin K) (hneq : θ a≠φ a) : N a≠⊤ := by
    have hk : klDiv (F.arm (θ a)) (F.arm (φ a))≠0 := by
      rw [kl_cost]
      exact (ENNReal.ofReal_pos.mpr (informationCost_pos F θ φ a hneq)).ne'
    intro h
    apply hprod a
    simp [h,hk]
  have hpfin (a : Fin K) : mp a≠⊤ :=
    ne_of_lt ((lintegral_ofReal_le_lintegral_enorm _).trans_lt (oneLLR_integrable F θ φ a).hasFiniteIntegral)
  have hmfin (a : Fin K) : mm a≠⊤ :=
    ne_of_lt ((lintegral_ofReal_le_lintegral_enorm _).trans_lt (oneLLR_integrable F θ φ a).neg.hasFiniteIntegral)
  have hpn (a : Fin K) : mp a*N a≠⊤ := by
    by_cases h : θ a=φ a
    · have hz : mp a=0 := by simp [mp,gp,oneLLR,h]
      simp [hz]
    · exact ENNReal.mul_ne_top (hpfin a) (hn a h)
  have hmn (a : Fin K) : mm a*N a≠⊤ := by
    by_cases h : θ a=φ a
    · have hz : mm a=0 := by simp [mm,gm,oneLLR,h]
      simp [hz]
    · exact ENNReal.mul_ne_top (hmfin a) (hn a h)
  have hpmeas : Measurable gp := ENNReal.measurable_ofReal.comp (oneLLR_measurable F θ φ)
  have hmmeas : Measurable gm := ENNReal.measurable_ofReal.comp (oneLLR_measurable F θ φ).neg
  have hlevels (n : ℕ) : MeasurableSet {ω | (n : ℕ∞)<τ ω} := by
    have h : MeasurableSet[banditFiltration K n] {ω | τ ω≤(n : ℕ∞)} := hτ n
    have heq : {ω | (n : ℕ∞)<τ ω}={ω | τ ω≤(n : ℕ∞)}ᶜ := by
      ext ω
      change (n : ℕ∞)<τ ω ↔ ¬τ ω≤(n : ℕ∞)
      exact lt_iff_not_ge
    rw [heq]
    exact (banditFiltration K).le n _ h.compl
  have hpR : Measurable (stoppedReward τ gp) :=
    Measurable.tsum (fun n => (hpmeas.comp (measurable_pi_apply n)).indicator (hlevels n))
  have hmR : Measurable (stoppedReward τ gm) :=
    Measurable.tsum (fun n => (hmmeas.comp (measurable_pi_apply n)).indicator (hlevels n))
  have hpval : (∫⁻ ω,stoppedReward τ gp ω ∂P)=∑ a : Fin K,mp a*N a :=
    stopped_reward_counts ν π hτ hfin gp hpmeas
  have hmval : (∫⁻ ω,stoppedReward τ gm ω ∂P)=∑ a : Fin K,mm a*N a :=
    stopped_reward_counts ν π hτ hfin gm hmmeas
  have hpint : (∫⁻ ω,stoppedReward τ gp ω ∂P)≠⊤ := by
    rw [hpval]
    exact ENNReal.sum_ne_top.mpr (fun a _ => hpn a)
  have hmint : (∫⁻ ω,stoppedReward τ gm ω ∂P)≠⊤ := by
    rw [hmval]
    exact ENNReal.sum_ne_top.mpr (fun a _ => hmn a)
  have hip := integrable_toReal_of_lintegral_ne_top hpR.aemeasurable hpint
  have him := integrable_toReal_of_lintegral_ne_top hmR.aemeasurable hmint
  have heq : stoppedLLR F θ φ τ=ᵐ[P] fun ω =>
      (stoppedReward τ gp ω).toReal-(stoppedReward τ gm ω).toReal := by
    filter_upwards [hfin] with ω hω
    exact stoppedLLR_parts F θ φ τ ω hω
  have hi : Integrable (stoppedLLR F θ φ τ) P := (hip.sub him).congr heq.symm
  refine ⟨hi,?_⟩
  change (∫ ω,stoppedLLR F θ φ τ ω ∂P)=_
  rw [integral_congr_ae heq,integral_sub hip him,
    integral_toReal hpR.aemeasurable (ae_lt_top hpR hpint),
    integral_toReal hmR.aemeasurable (ae_lt_top hmR hmint),hpval,hmval,
    ENNReal.toReal_sum (fun a _ => hpn a),ENNReal.toReal_sum (fun a _ => hmn a),
    ←Finset.sum_sub_distrib,ENNReal.toReal_sum (fun a _ => hprod a)]
  apply Finset.sum_congr rfl
  intro a ha
  have hmean : (mp a).toReal-(mm a).toReal=informationCost F θ φ a := by
    exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part (oneLLR_integrable F θ φ a)).symm.trans
      (oneLLR_mean F θ φ a)
  rw [kl_cost,ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_mul,
    ←sub_mul,hmean,ENNReal.toReal_ofReal (informationCost_nonneg F θ φ a)]

end OptimalBAI.LowerBound


open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal
set_option maxHeartbeats 2000000
namespace OptimalBAI.LowerBound

lemma stopped_measure_density (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ) (π : BanditPolicy K)
    {τ : (ℕ → Fin K × ℝ) → ℕ∞} (hτ : IsBanditStoppingTime τ)
    (hθ : ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F θ) π,τ ω≠⊤)
    (hφ : ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F φ) π,τ ω≠⊤) :
    ((banditTrajMeasure (expFamilyBandit F φ) π).trim hτ.measurableSpace_le).withDensity
      (stoppedDensity F θ φ τ)=
      (banditTrajMeasure (expFamilyBandit F θ) π).trim hτ.measurableSpace_le := by
  refine @Measure.ext _ hτ.measurableSpace _ _ ?_
  intro A hA
  rw [withDensity_apply _ hA,←lintegral_indicator hA,
    lintegral_trim hτ.measurableSpace_le ((stoppedDensity_measurable F θ φ hτ).indicator hA),
    trim_measurableSet_eq _ hA]
  exact (stopped_event_density F θ φ π hτ hθ hφ A hA).symm

lemma stopped_llr (F : ExpFamily) {K : ℕ} (θ φ : Fin K → F.Θ) (π : BanditPolicy K)
    {τ : (ℕ → Fin K × ℝ) → ℕ∞} (hτ : IsBanditStoppingTime τ)
    (hθ : ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F θ) π,τ ω≠⊤)
    (hφ : ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F φ) π,τ ω≠⊤) :
    @llr _ hτ.measurableSpace
      ((banditTrajMeasure (expFamilyBandit F θ) π).trim hτ.measurableSpace_le)
      ((banditTrajMeasure (expFamilyBandit F φ) π).trim hτ.measurableSpace_le)=ᵐ[
        (banditTrajMeasure (expFamilyBandit F θ) π).trim hτ.measurableSpace_le]
      stoppedLLR F θ φ τ := by
  let P := (banditTrajMeasure (expFamilyBandit F θ) π).trim hτ.measurableSpace_le
  let Q := (banditTrajMeasure (expFamilyBandit F φ) π).trim hτ.measurableSpace_le
  have hd : Q.withDensity (stoppedDensity F θ φ τ)=P := stopped_measure_density F θ φ π hτ hθ hφ
  have hac : P≪Q := by rw [←hd]; exact withDensity_absolutelyContinuous _ _
  letI : MeasurableSpace (ℕ → Fin K × ℝ) := hτ.measurableSpace
  have hrn := Measure.rnDeriv_withDensity Q (stoppedDensity_measurable F θ φ hτ)
  rw [hd] at hrn
  filter_upwards [hac.ae_le hrn] with ω hω
  change Real.log (P.rnDeriv Q ω).toReal=stoppedLLR F θ φ τ ω
  simp only [hω,stoppedDensity,ENNReal.toReal_ofReal (Real.exp_pos _).le,Real.log_exp]

end OptimalBAI.LowerBound


open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal
set_option maxHeartbeats 2000000
namespace OptimalBAI.LowerBound

lemma exp_density_variational {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (L f : Ω → ℝ) (hL : Measurable L) (hf : Measurable f) (hLi : Integrable L P)
    (hfi : Integrable f P) (hefi : Integrable (fun ω => Real.exp (f ω)) Q)
    (hd : Q.withDensity (fun ω => ENNReal.ofReal (Real.exp (L ω)))=P)
    (hsub : (∫ ω,Real.exp (f ω) ∂Q)≤1) :
    (∫ ω,f ω ∂P)≤∫ ω,L ω ∂P := by
  let V := Q.withDensity (fun ω => ENNReal.ofReal (Real.exp (f ω)))
  have hV : V Set.univ=ENNReal.ofReal (∫ ω,Real.exp (f ω) ∂Q) := by
    dsimp only [V]
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ←ofReal_integral_eq_lintegral_ofReal hefi (ae_of_all _ (fun ω => (Real.exp_pos _).le))]
  have hVle : V Set.univ≤1 := by rw [hV]; exact ENNReal.ofReal_le_one.mpr hsub
  letI : IsFiniteMeasure V := ⟨hVle.trans_lt ENNReal.one_lt_top⟩
  have heq : V.withDensity (fun ω => ENNReal.ofReal (Real.exp (L ω-f ω)))=P := by
    dsimp only [V]
    rw [←withDensity_mul _ (by fun_prop) (by fun_prop)]
    convert hd using 1
    congr 1
    funext ω
    rw [Pi.mul_apply,←ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add]
    congr 2
    ring
  have hac : P≪V := by rw [←heq]; exact withDensity_absolutelyContinuous _ _
  have hrn := Measure.rnDeriv_withDensity V
    (f := fun ω => ENNReal.ofReal (Real.exp (L ω-f ω))) (by fun_prop)
  rw [heq] at hrn
  have hllr : llr P V=ᵐ[P] fun ω => L ω-f ω := by
    filter_upwards [hac.ae_le hrn] with ω hω
    simp only [llr_def,hω,ENNReal.toReal_ofReal (Real.exp_pos _).le,Real.log_exp]
  have hi : Integrable (llr P V) P := (hLi.sub hfi).congr hllr.symm
  have hg := integral_llr_add_sub_measure_univ_nonneg hac hi
  rw [integral_congr_ae hllr,integral_sub hLi hfi,(show P.real Set.univ=1 from probReal_univ)] at hg
  have hvreal : V.real Set.univ≤1 := by
    rw [measureReal_def]
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mpr hVle
  linarith

lemma binary_information {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (L : Ω → ℝ) (hL : Measurable L) (hLi : Integrable L P)
    (hd : Q.withDensity (fun ω => ENNReal.ofReal (Real.exp (L ω)))=P)
    (A : Set Ω) (hA : MeasurableSet A) (δ : ℝ) (hδ : 0<δ) (hδhalf : δ≤1/2)
    (hp : 1-δ≤P.real A) (hq : Q.real A≤δ) :
    bernoulliRelativeEntropy δ (1-δ)≤∫ ω,L ω ∂P := by
  classical
  have hα : 0<1-δ := by linarith
  let r := (1-δ)/δ
  let c := Real.log r
  let f := fun ω : Ω => if ω∈A then c else -c
  have hrpos : 0<r := div_pos hα hδ
  have hr1 : 1≤r := by dsimp [r]; rw [le_div_iff₀ hδ]; linarith
  have hc : 0≤c := Real.log_nonneg hr1
  have hcexp : Real.exp c=r := Real.exp_log hrpos
  have hnegexp : Real.exp (-c)=r⁻¹ := by rw [Real.exp_neg,hcexp]
  have hf : Measurable f := measurable_const.ite hA measurable_const
  have hfi : Integrable f P := Integrable.piecewise hA (integrable_const c) (integrable_const (-c))
  have heqexp : (fun ω => Real.exp (f ω))=A.piecewise (fun _ => Real.exp c) (fun _ => Real.exp (-c)) := by
    funext ω
    by_cases h : ω∈A <;> simp [f,Set.piecewise,h]
  have hefi : Integrable (fun ω => Real.exp (f ω)) Q := by
    rw [heqexp]
    exact Integrable.piecewise hA (integrable_const (Real.exp c)) (integrable_const (Real.exp (-c)))
  have hexp : (∫ ω,Real.exp (f ω) ∂Q)=Q.real A*r+(1-Q.real A)*r⁻¹ := by
    rw [heqexp,integral_piecewise hA (integrable_const _).integrableOn (integrable_const _).integrableOn,
      setIntegral_const,setIntegral_const,probReal_compl_eq_one_sub hA,hcexp,hnegexp]
    rfl
  have hfintegral : (∫ ω,f ω ∂P)=P.real A*c+(1-P.real A)*(-c) := by
    change (∫ ω,A.piecewise (fun _ => c) (fun _ => -c) ω ∂P)=_
    rw [integral_piecewise hA (integrable_const _).integrableOn (integrable_const _).integrableOn,
      setIntegral_const,setIntegral_const,probReal_compl_eq_one_sub hA]
    rfl
  have hrinv : r⁻¹≤1 := inv_le_one_of_one_le₀ hr1
  have hcoef : 0≤r-r⁻¹ := by linarith
  have hδeval : δ*r+(1-δ)*r⁻¹=1 := by
    dsimp [r]
    field_simp
    <;> ring
  have hsub : (∫ ω,Real.exp (f ω) ∂Q)≤1 := by
    rw [hexp,←hδeval]
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) hcoef]
  have hv := exp_density_variational P Q L f hL hf hLi hfi hefi hd hsub
  rw [hfintegral] at hv
  have hbern : bernoulliRelativeEntropy δ (1-δ)=(1-2*δ)*c := by
    unfold bernoulliRelativeEntropy
    have heq : 1-(1-δ)=δ := by ring
    rw [heq,Real.log_div (ne_of_gt hδ) (ne_of_gt hα),
      Real.log_div (ne_of_gt hα) (ne_of_gt hδ)]
    dsimp [c,r]
    rw [Real.log_div (ne_of_gt hα) (ne_of_gt hδ)]
    ring
  rw [hbern]
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) hc]

end OptimalBAI.LowerBound


open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal
set_option maxHeartbeats 2000000
namespace OptimalBAI.LowerBound

lemma bandit_means (F : ExpFamily) {K : ℕ} (θ : Fin K → F.Θ) (a : Fin K) :
    banditArmMean (expFamilyBandit F θ) a=deriv F.b (θ a) :=
  F.mean_integral (θ a) (θ a).2

lemma best_mean (F : ExpFamily) {K : ℕ} (θ : Fin K → F.Θ) (a : Fin K) (ha : F.IsBestArm θ a) :
    banditOptimalMean (expFamilyBandit F θ)=deriv F.b (θ a) := by
  letI : Nonempty (Fin K) := ⟨a⟩
  unfold banditOptimalMean
  simp_rw [bandit_means]
  apply le_antisymm
  · apply ciSup_le
    intro i
    by_cases hi : i=a
    · simp [hi]
    · exact (ha i hi).le
  · exact le_ciSup (Set.finite_range (fun i => deriv F.b (θ i))).bddAbove a

lemma best_gap_iff (F : ExpFamily) {K : ℕ} (θ : Fin K → F.Θ) (a : Fin K)
    (ha : F.IsBestArm θ a) (i : Fin K) :
    0<banditGap (expFamilyBandit F θ) i ↔ i≠a := by
  rw [banditGap,best_mean F θ a ha,bandit_means,sub_pos]
  constructor
  · intro h hi
    simpa [hi] using h
  · exact ha i

lemma pac_error_le (F : ExpFamily) {K : ℕ} (S : Set (Fin K → F.Θ))
    (δ : ℝ) (π : BanditPolicy K) (τ : (ℕ → Fin K × ℝ) → ℕ∞)
    (ψ : (ℕ → Fin K × ℝ) → Fin K)
    (hPAC : IsDeltaPAC δ π τ ψ (expFamilyBandit F '' S))
    (θ : Fin K → F.Θ) (hθ : θ∈S) (a : Fin K) (ha : F.IsBestArm θ a) :
    banditTrajMeasure (expFamilyBandit F θ) π {ω | ψ ω≠a}≤ENNReal.ofReal δ := by
  have hmem : expFamilyBandit F θ∈expFamilyBandit F '' S := ⟨θ,hθ,rfl⟩
  have heq : {ω | ψ ω≠a}=ᵐ[banditTrajMeasure (expFamilyBandit F θ) π]
      {ω | τ ω<⊤ ∧ 0<banditGap (expFamilyBandit F θ) (ψ ω)} := by
    filter_upwards [hPAC.1 _ hmem] with ω hω
    change (ψ ω≠a)=(τ ω<⊤ ∧ 0<banditGap (expFamilyBandit F θ) (ψ ω))
    apply propext
    rw [best_gap_iff F θ a ha]
    simp only [hω,true_and]
  rw [measure_congr heq]
  exact hPAC.2 _ hmem

end OptimalBAI.LowerBound


open MeasureTheory ENNReal InformationTheory BanditAlgorithm
open scoped ENNReal
set_option maxHeartbeats 2000000
namespace OptimalBAI.LowerBound

/-- Eq. (2) of Garivier–Kaufmann (arXiv:1602.04589v2, p. 4), the transportation inequality
(Lemma 1 of Kaufmann, Cappé, Garivier 2015), for `δ ∈ (0, 1/2]`. Let `𝒮` be any set of
exponential-family bandit models each with a unique optimal arm, `(π, τ, ψ)` a `δ`-PAC strategy on
`𝒮`, and `μ, λ ∈ 𝒮` with different optimal arms. Then
`∑_a d(μ_a, λ_a) E_μ[N_a(τ)] ≥ kl(δ, 1 - δ)`, with `d(μ_a, λ_a) = KL(ν_{θ_a}, ν_{θ'_a})` and
`N_a(τ)` the number of draws of arm `a` in the first `τ` rounds.

`(τ ω).toNat` is `0` when `τ ω = ⊤`; that event is null by the `δ`-PAC hypothesis. As in
Theorem 1, `δ ≤ 1/2` is added (false for `δ ∈ (1/2, 1)`). -/
theorem transportation_inequality {K : ℕ} (F : ExpFamily) (S : Set (Fin K → F.Θ))
    (hS : ∀ θ ∈ S, ∃ a, F.IsBestArm θ a)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1 / 2)
    (π : BanditPolicy K) (τ : (ℕ → Fin K × ℝ) → ℕ∞) (ψ : (ℕ → Fin K × ℝ) → Fin K)
    (hτ : IsBanditStoppingTime τ) (hψ : Measurable[hτ.measurableSpace] ψ)
    (hPAC : IsDeltaPAC δ π τ ψ (expFamilyBandit F '' S))
    (θ θ' : Fin K → F.Θ) (hθ : θ ∈ S) (hθ' : θ' ∈ S)
    (hdiff : ∀ a, F.IsBestArm θ a → ¬ F.IsBestArm θ' a) :
    ENNReal.ofReal (bernoulliRelativeEntropy δ (1 - δ)) ≤
      ∑ a, klDiv ((expFamilyBandit F θ).P a) ((expFamilyBandit F θ').P a) *
        ∫⁻ ω, (trajPullCount a (τ ω).toNat ω : ℝ≥0∞)
          ∂banditTrajMeasure (expFamilyBandit F θ) π := by
  classical
  let ν := expFamilyBandit F θ
  let ν' := expFamilyBandit F θ'
  let P₀ := banditTrajMeasure ν π
  let Q₀ := banditTrajMeasure ν' π
  let total := ∑ a : Fin K,klDiv (ν.P a) (ν'.P a)*
    ∫⁻ ω,(trajPullCount a (τ ω).toNat ω : ℝ≥0∞) ∂P₀
  change ENNReal.ofReal (bernoulliRelativeEntropy δ (1-δ))≤total
  by_cases htop : total=⊤
  · simp [htop]
  have hθfin : ∀ᵐ ω ∂P₀,τ ω≠⊤ :=
    (hPAC.1 ν ⟨θ,hθ,rfl⟩).mono (fun _ h => ne_of_lt h)
  have hθ'fin : ∀ᵐ ω ∂Q₀,τ ω≠⊤ :=
    (hPAC.1 ν' ⟨θ',hθ',rfl⟩).mono (fun _ h => ne_of_lt h)
  obtain ⟨a,ha⟩ := hS θ hθ
  obtain ⟨b,hb⟩ := hS θ' hθ'
  have hab : a≠b := fun h => hdiff a ha (h.symm ▸ hb)
  let A := {ω | ψ ω=a}
  have hA : MeasurableSet[hτ.measurableSpace] A := hψ (measurableSet_singleton a)
  have hAg : MeasurableSet A := hτ.measurableSpace_le _ hA
  have hpa : P₀ Aᶜ≤ENNReal.ofReal δ := pac_error_le F S δ π τ ψ hPAC θ hθ a ha
  have hqb : Q₀ A≤ENNReal.ofReal δ :=
    (measure_mono (show A⊆{ω | ψ ω≠b} from fun ω hω => by
      change ψ ω=a at hω
      change ψ ω≠b
      rw [hω]
      exact hab)).trans (pac_error_le F S δ π τ ψ hPAC θ' hθ' b hb)
  have hpaReal : P₀.real Aᶜ≤δ := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hpa
    simpa only [measureReal_def,ENNReal.toReal_ofReal hδ_pos.le] using h
  have hqbReal : Q₀.real A≤δ := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hqb
    simpa only [measureReal_def,ENNReal.toReal_ofReal hδ_pos.le] using h
  have hpReal : 1-δ≤P₀.real A := by
    rw [probReal_compl_eq_one_sub hAg] at hpaReal
    linarith
  have hw := stopped_llr_integral F θ θ' π hτ hθfin htop
  have hLm := stoppedLLR_measurable F θ θ' hτ
  let P := P₀.trim hτ.measurableSpace_le
  let Q := Q₀.trim hτ.measurableSpace_le
  have hLi : Integrable (stoppedLLR F θ θ' τ) P :=
    Integrable.trim hτ.measurableSpace_le hw.1 hLm.stronglyMeasurable
  have hi : (∫ ω,stoppedLLR F θ θ' τ ω ∂P₀)=∫ ω,stoppedLLR F θ θ' τ ω ∂P :=
    integral_trim hτ.measurableSpace_le hLm.stronglyMeasurable
  have hsum : ENNReal.ofReal (∫ ω,stoppedLLR F θ θ' τ ω ∂P₀)=total := by
    rw [hw.2]
    exact ENNReal.ofReal_toReal htop
  have hpTrim : 1-δ≤P.real A := by
    change 1-δ≤((P₀.trim hτ.measurableSpace_le) A).toReal
    rw [trim_measurableSet_eq _ hA]
    exact hpReal
  have hqTrim : Q.real A≤δ := by
    change ((Q₀.trim hτ.measurableSpace_le) A).toReal≤δ
    rw [trim_measurableSet_eq _ hA]
    exact hqbReal
  have hPprob : @IsProbabilityMeasure _ hτ.measurableSpace P := ⟨by
    change (P₀.trim hτ.measurableSpace_le) Set.univ=1
    rw [trim_measurableSet_eq _ MeasurableSet.univ]
    exact measure_univ⟩
  have hQprob : @IsProbabilityMeasure _ hτ.measurableSpace Q := ⟨by
    change (Q₀.trim hτ.measurableSpace_le) Set.univ=1
    rw [trim_measurableSet_eq _ MeasurableSet.univ]
    exact measure_univ⟩
  have hd := stopped_measure_density F θ θ' π hτ hθfin hθ'fin
  letI : MeasurableSpace (ℕ → Fin K × ℝ) := hτ.measurableSpace
  letI : IsProbabilityMeasure P := hPprob
  letI : IsProbabilityMeasure Q := hQprob
  have hbound := binary_information P Q (stoppedLLR F θ θ' τ) hLm hLi hd A hA
    δ hδ_pos hδ_le hpTrim hqTrim
  rw [←hi] at hbound
  rw [←hsum]
  exact ENNReal.ofReal_le_ofReal hbound

end OptimalBAI.LowerBound



open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal
set_option maxHeartbeats 2000000
namespace OptimalBAI.LowerBound

lemma trajPullCount_sum {K : ℕ} (ω : ℕ → Fin K × ℝ) (t : ℕ) :
    ∑ a : Fin K,trajPullCount a t ω=t := by
  classical
  unfold trajPullCount
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  simp

lemma stopped_count_measurable {K : ℕ} {τ : (ℕ → Fin K × ℝ) → ℕ∞}
    (hτ : IsBanditStoppingTime τ) (a : Fin K) :
    Measurable (fun ω => (trajPullCount a (τ ω).toNat ω : ℝ≥0∞)) := by
  have hm : Measurable (fun ω => (τ ω).toNat) := hτ.measurable'.untopD 0
  have hcount (n : ℕ) : Measurable (trajPullCount a n) := by
    simpa only [Function.comp_def,OptimalBAI.TrackStop.histPulls_prefix] using
      (OptimalBAI.TrackStop.histPulls_measurable (n := n) a).comp measurable_banditTrajPrefix
  have hc : Measurable (fun ω => trajPullCount a (τ ω).toNat ω) :=
    (show Measurable (fun p : ℕ × (ℕ → Fin K × ℝ) => trajPullCount a p.1 p.2) from
      measurable_from_prod_countable_right hcount).comp (hm.prodMk measurable_id)
  exact (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp hc

lemma expected_count_sum {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K)
    {τ : (ℕ → Fin K × ℝ) → ℕ∞} (hτ : IsBanditStoppingTime τ)
    (hfin : ∀ᵐ ω ∂banditTrajMeasure ν π,τ ω≠⊤) :
    (∑ a : Fin K,∫⁻ ω,(trajPullCount a (τ ω).toNat ω : ℝ≥0∞) ∂banditTrajMeasure ν π)=
      ∫⁻ ω,(τ ω : ℝ≥0∞) ∂banditTrajMeasure ν π := by
  rw [←lintegral_finsetSum _ (fun a _ => stopped_count_measurable hτ a)]
  apply lintegral_congr_ae
  filter_upwards [hfin] with ω hω
  have hsum : (∑ a : Fin K,(trajPullCount a (τ ω).toNat ω : ℝ≥0∞))=((τ ω).toNat : ℝ≥0∞) := by
    exact_mod_cast trajPullCount_sum ω (τ ω).toNat
  rw [hsum,←ENat.natCast_toNat hω]
  simp

end OptimalBAI.LowerBound


open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal
set_option maxHeartbeats 2000000
namespace OptimalBAI.LowerBound

lemma best_in_optimal (F : ExpFamily) {K : ℕ} (θ : Fin K → F.Θ)
    (a : Fin K) (ha : F.IsBestArm θ a) :
    a∈banditOptimalArms (expFamilyBandit F θ) := by
  change banditArmMean (expFamilyBandit F θ) a=banditOptimalMean (expFamilyBandit F θ)
  rw [bandit_means,best_mean F θ a ha]

lemma alternative_different_best (F : ExpFamily) {K : ℕ} (S : Set (Fin K → F.Θ))
    (θ φ : Fin K → F.Θ)
    (h : expFamilyBandit F φ∈baiAlternatives (expFamilyBandit F '' S) (expFamilyBandit F θ)) :
    ∀ a,F.IsBestArm θ a → ¬F.IsBestArm φ a := by
  intro a hθ hφ
  exact Set.disjoint_left.mp h.2 (best_in_optimal F φ a hφ) (best_in_optimal F θ a hθ)

end OptimalBAI.LowerBound


open scoped ENNReal NNReal
set_option maxHeartbeats 2000000
namespace OptimalBAI.LowerBound

lemma allocation_lower_bound {K : ℕ} {X : Type*} (E : Set X) (D : X → Fin K → ℝ≥0∞)
    (N : Fin K → ℝ≥0∞) (T q : ℝ≥0∞) (hT0 : T≠0) (hTtop : T≠⊤) (hq0 : q≠0)
    (hqtop : q≠⊤) (hsum : ∑ a,N a=T) (hinfo : ∀ x∈E,q≤∑ a,D x a*N a) :
    (⨆ α∈{α : Fin K → ℝ≥0 | ∑ a,α a=1},⨅ x∈E,∑ a,(α a : ℝ≥0∞)*D x a)⁻¹*q≤T := by
  classical
  have hN (a : Fin K) : N a≠⊤ := by
    have hle : N a≤T := (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ a)).trans hsum.le
    exact ne_of_lt (hle.trans_lt hTtop.lt_top)
  let α := fun a => (N a/T).toNNReal
  have hdiv (a : Fin K) : N a/T≠⊤ := ENNReal.div_ne_top (hN a) hT0
  have hcoe (a : Fin K) : (α a : ℝ≥0∞)=N a/T := ENNReal.coe_toNNReal (hdiv a)
  have hα : ∑ a,α a=1 := by
    apply ENNReal.coe_injective
    simp only [ENNReal.ofNNReal_finsetSum,ENNReal.coe_one,hcoe]
    simp only [div_eq_mul_inv]
    rw [←Finset.sum_mul,hsum,ENNReal.mul_inv_cancel hT0 hTtop]
  have hlower : q/T≤⨅ x∈E,∑ a,(α a : ℝ≥0∞)*D x a := by
    apply le_iInf
    intro x
    apply le_iInf
    intro hx
    have h := hinfo x hx
    have hd : q/T≤(∑ a,D x a*N a)/T := by gcongr
    refine hd.trans_eq ?_
    simp_rw [hcoe,div_eq_mul_inv]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    ac_rfl
  have hgame : q/T≤⨆ α∈{α : Fin K → ℝ≥0 | ∑ a,α a=1},⨅ x∈E,∑ a,(α a : ℝ≥0∞)*D x a :=
    hlower.trans (le_iSup_of_le α (le_iSup_of_le hα le_rfl))
  calc
    _≤(q/T)⁻¹*q := mul_le_mul' (ENNReal.inv_le_inv' hgame) le_rfl
    _=T := by
      rw [div_eq_mul_inv,ENNReal.mul_inv (Or.inl hq0) (Or.inl hqtop),inv_inv]
      rw [mul_comm q⁻¹ T,mul_assoc,ENNReal.inv_mul_cancel hq0 hqtop,mul_one]

end OptimalBAI.LowerBound


open MeasureTheory ENNReal InformationTheory BanditAlgorithm
open scoped ENNReal NNReal
set_option maxHeartbeats 2000000
namespace OptimalBAI.LowerBound

/-- Theorem 1 of Garivier–Kaufmann (arXiv:1602.04589v2, p. 3, with eq. (1) on p. 4), for
`δ ∈ (0, 1/2]`. Let `𝒮` be any set of exponential-family bandit models each of which has a unique
optimal arm. For every `δ`-PAC strategy `(π, τ, ψ)` on `𝒮` and every `μ ∈ 𝒮`,
`E_μ[τ] ≥ T*(μ) · kl(δ, 1 - δ)`, where `T*(μ)` is the characteristic time of eq. (1)
(`baiComplexity`, with `d = KL` of the arm laws).

Printed slip handled: the paper states `δ ∈ (0, 1)`; the statement is false for `δ ∈ (1/2, 1)`
(its proof uses `kl(1-δ, δ) ≥ kl(δ, 1-δ)`-monotonicity valid only for `δ ≤ 1/2`), so `δ ≤ 1/2`
is assumed. Arms are 0-based. Expectations and `T*` are in `ℝ≥0∞`. -/
theorem sample_complexity_lower_bound {K : ℕ} (F : ExpFamily) (S : Set (Fin K → F.Θ))
    (hS : ∀ θ ∈ S, ∃ a, F.IsBestArm θ a)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1 / 2)
    (π : BanditPolicy K) (τ : (ℕ → Fin K × ℝ) → ℕ∞) (ψ : (ℕ → Fin K × ℝ) → Fin K)
    (hτ : IsBanditStoppingTime τ) (hψ : Measurable[hτ.measurableSpace] ψ)
    (hPAC : IsDeltaPAC δ π τ ψ (expFamilyBandit F '' S))
    (θ : Fin K → F.Θ) (hθ : θ ∈ S) :
    baiComplexity (expFamilyBandit F θ) (expFamilyBandit F '' S) *
        ENNReal.ofReal (bernoulliRelativeEntropy δ (1 - δ)) ≤
      ∫⁻ ω, (τ ω : ℝ≥0∞) ∂banditTrajMeasure (expFamilyBandit F θ) π := by
  classical
  let ν := expFamilyBandit F θ
  letI : Nonempty (StochasticBandit K) := ⟨ν⟩
  let E := baiAlternatives (expFamilyBandit F '' S) ν
  let P := banditTrajMeasure ν π
  let T := ∫⁻ ω,(τ ω : ℝ≥0∞) ∂P
  let N := fun a : Fin K => ∫⁻ ω,(trajPullCount a (τ ω).toNat ω : ℝ≥0∞) ∂P
  let q := ENNReal.ofReal (bernoulliRelativeEntropy δ (1-δ))
  change baiComplexity ν (expFamilyBandit F '' S)*q≤T
  by_cases hq : q=0
  · simp [hq]
  by_cases hTtop : T=⊤
  · simp [hTtop]
  have hfin : ∀ᵐ ω ∂P,τ ω≠⊤ := (hPAC.1 ν ⟨θ,hθ,rfl⟩).mono (fun _ h => ne_of_lt h)
  have hsum : ∑ a,N a=T := expected_count_sum ν π hτ hfin
  have hinfo (ν' : StochasticBandit K) (hν' : ν'∈E) : q≤∑ a,klDiv (ν.P a) (ν'.P a)*N a := by
    obtain ⟨φ,hφ,rfl⟩ := hν'.1
    exact transportation_inequality F S hS δ hδ_pos hδ_le π τ ψ hτ hψ hPAC θ φ hθ hφ
      (alternative_different_best F S θ φ hν')
  obtain ⟨a,ha⟩ := hS θ hθ
  by_cases hE : E.Nonempty
  · obtain ⟨ν',hν'⟩ := hE
    have hT0 : T≠0 := by
      intro hzero
      have hnzero (b : Fin K) : N b=0 := by
        apply le_antisymm _ bot_le
        have hle : N b≤∑ c,N c := Finset.single_le_sum (fun c _ => (show 0≤N c from bot_le)) (Finset.mem_univ b)
        exact hle.trans (hsum.trans hzero).le
      have h := hinfo ν' hν'
      simp only [hnzero,mul_zero,Finset.sum_const_zero] at h
      exact hq (le_antisymm h bot_le)
    exact allocation_lower_bound E (fun ν' a => klDiv (ν.P a) (ν'.P a)) N T q hT0 hTtop hq
      ENNReal.ofReal_ne_top hsum hinfo
  · have heq : E=∅ := Set.not_nonempty_iff_eq_empty.mp hE
    let α := fun b : Fin K => if b=a then (1 : ℝ≥0) else 0
    have hα : ∑ b,α b=1 := by simp [α]
    have hsup : (⨆ α∈{α : Fin K → ℝ≥0 | ∑ b,α b=1},
        ⨅ ν'∈E,∑ b,(α b : ℝ≥0∞)*klDiv (ν.P b) (ν'.P b))=⊤ := by
      apply top_unique
      apply le_iSup_of_le α
      apply le_iSup_of_le hα
      simp only [heq,Set.mem_empty_iff_false,iInf_false,iInf_const,le_refl]
    change (⨆ α∈{α : Fin K → ℝ≥0 | ∑ b,α b=1},
      ⨅ ν'∈E,∑ b,(α b : ℝ≥0∞)*klDiv (ν.P b) (ν'.P b))⁻¹*q≤T
    rw [hsup,ENNReal.inv_top,zero_mul]
    exact bot_le

end OptimalBAI.LowerBound


open MeasureTheory InformationTheory BanditAlgorithm OptimalBAI.LowerBound
open scoped ENNReal NNReal
theorem solution {K : ℕ} (F : ExpFamily) (S : Set (Fin K → F.Θ))
    (hS : ∀ θ ∈ S, ∃ a, F.IsBestArm θ a)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1 / 2)
    (π : BanditPolicy K) (τ : (ℕ → Fin K × ℝ) → ℕ∞) (ψ : (ℕ → Fin K × ℝ) → Fin K)
    (hτ : IsBanditStoppingTime τ) (hψ : Measurable[hτ.measurableSpace] ψ)
    (hPAC : IsDeltaPAC δ π τ ψ (expFamilyBandit F '' S))
    (θ : Fin K → F.Θ) (hθ : θ ∈ S) :
    baiComplexity (expFamilyBandit F θ) (expFamilyBandit F '' S) *
        ENNReal.ofReal (bernoulliRelativeEntropy δ (1 - δ)) ≤
      ∫⁻ ω, (τ ω : ℝ≥0∞) ∂banditTrajMeasure (expFamilyBandit F θ) π := by
  exact sample_complexity_lower_bound F S hS δ hδ_pos hδ_le π τ ψ hτ hψ hPAC θ hθ

#print axioms solution
