-- Prove2me | solution 1 for OptimalBAI.OptProportions.g_strictMono_bijective
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T09:22:16.007315+00:00
-- url     : https://prove2.me/submissions/63a1c6fc-5d5e-4551-b721-6fe535a859bd

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

open OptimalBAI.OptProportions
theorem solution {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (a : Fin K) (ha : a ≠ 0) :
    StrictMonoOn (gFun F μ a) (Set.Ici 0) ∧
      gFun F μ a '' Set.Ici 0 = Set.Ico 0 (F.d (μ 0) (μ a)) := by
  exact ⟨gFun_strictMono F μ hμ hbest a ha, gFun_image F μ hμ hbest a ha⟩

#print axioms solution
