-- Prove2me | solution 1 for Plasticity.U16.linearize
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T08:09:44.742977+00:00
-- url     : https://prove2.me/submissions/839a1c6b-d50f-4534-b0a3-7823f3df5e97

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.UniformSpace.Cauchy
import Theorems.Thm_Plasticity_U16_norm_eq
import Theorems.Thm_Plasticity_U16_mixed_scale
import Theorems.Thm_Plasticity_U16_two_direction

open Filter Topology

namespace Sol_Plasticity_U16_linearize

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The conclusions of the three child cards, bundled. -/
structure Good (F : X → Y) : Prop where
  zero : F 0 = 0
  norm : ∀ x : X, ‖x‖ ≤ 1 → ‖F x‖ = ‖x‖
  mixed : ∀ v : X, ‖v‖ = 1 → ∀ t u : ℝ, 0 < t → t ≤ 1 → 0 < u → u ≤ 1 →
    ‖t⁻¹ • F (t • v) + u⁻¹ • F (-(u • v))‖ ≤ 8 * (t + u)
  two : ∀ v w : X, ‖v‖ ≤ 1 → ‖w‖ ≤ 1 → ∀ t : ℝ, 0 < t → t ≤ 1 / 2 →
    ‖F (t • v) + F (t • w) + F (-(t • (v + w)))‖ ≤ 96 * t ^ 2

/-- Difference quotient `t⁻¹ F(t v)`. -/
noncomputable def H (F : X → Y) (v : X) (t : ℝ) : Y := t⁻¹ • F (t • v)

lemma H_neg (F : X → Y) (v : X) (t : ℝ) : H F (-v) t = t⁻¹ • F (-(t • v)) := by
  simp only [H, smul_neg]

lemma H_smul (F : X → Y) (v : X) {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    H F (c • v) t = c • H F v (c * t) := by
  simp only [H, smul_smul, mul_inv, mul_inv_cancel_left₀ hc]
  rw [mul_comm c t]

lemma H_zero {F : X → Y} (hF : Good F) (t : ℝ) : H F 0 t = 0 := by
  simp [H, hF.zero]

lemma tendsto_const_mul_zero (c : ℝ) : Tendsto (fun t : ℝ => c * t) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => c * t) (𝓝 0) (𝓝 (c * 0)) := tendsto_const_nhds.mul tendsto_id
  rw [mul_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

lemma tendsto_mul_nhdsGT {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => c * t) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_const_mul_zero c, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact Set.mem_Ioi.2 (mul_pos hc ht)

variable {F : X → Y}

lemma H_add_neg_unit (hF : Good F) {u : X} (hu : ‖u‖ = 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ‖H F u t + H F (-u) t‖ ≤ 16 * t := by
  have h := hF.mixed u hu t t ht0 ht1 ht0 ht1
  rw [H_neg]
  simp only [H]
  linarith

lemma H_sub_unit (hF : Good F) {u : X} (hu : ‖u‖ = 1) {t s : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hs0 : 0 < s) (hs1 : s ≤ 1) : ‖H F u t - H F u s‖ ≤ 8 * t + 24 * s := by
  have h1 := hF.mixed u hu t s ht0 ht1 hs0 hs1
  have h2 := H_add_neg_unit hF hu hs0 hs1
  rw [H_neg] at h2
  have e : H F u t - H F u s = (t⁻¹ • F (t • u) + s⁻¹ • F (-(s • u)))
      - (H F u s + s⁻¹ • F (-(s • u))) := by
    simp only [H]; abel
  rw [e]
  calc _ ≤ ‖t⁻¹ • F (t • u) + s⁻¹ • F (-(s • u))‖ + ‖H F u s + s⁻¹ • F (-(s • u))‖ :=
        norm_sub_le _ _
    _ ≤ 8 * (t + s) + 16 * s := add_le_add h1 h2
    _ = 8 * t + 24 * s := by ring

lemma exists_lim_unit [CompleteSpace Y] (hF : Good F) {u : X} (hu : ‖u‖ = 1) :
    ∃ L, Tendsto (H F u) (𝓝[>] 0) (𝓝 L) := by
  refine cauchy_map_iff_exists_tendsto.1 (Metric.cauchy_iff.2 ⟨inferInstance, fun ε hε => ?_⟩)
  have hδ0 : 0 < min 1 (ε / 64) := lt_min one_pos (by positivity)
  have h1 : min 1 (ε / 64) ≤ 1 := min_le_left _ _
  have h2 : min 1 (ε / 64) ≤ ε / 64 := min_le_right _ _
  refine ⟨H F u '' Set.Ioo 0 (min 1 (ε / 64)), image_mem_map (Ioo_mem_nhdsGT hδ0), ?_⟩
  rintro _ ⟨t, ⟨ht0, htδ⟩, rfl⟩ _ ⟨s, ⟨hs0, hsδ⟩, rfl⟩
  rw [dist_eq_norm]
  have := H_sub_unit hF hu ht0 (by linarith) hs0 (by linarith)
  linarith

lemma tendsto_H_smul {v : X} {c : ℝ} (hc : 0 < c) {L : Y}
    (h : Tendsto (H F v) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (H F (c • v)) (𝓝[>] 0) (𝓝 (c • L)) := by
  have e : H F (c • v) = fun t => c • H F v (c * t) := funext (H_smul F v hc.ne')
  rw [e]
  exact (h.comp (tendsto_mul_nhdsGT hc)).const_smul c

lemma exists_lim [CompleteSpace Y] (hF : Good F) (v : X) :
    ∃ L, Tendsto (H F v) (𝓝[>] 0) (𝓝 L) := by
  by_cases hv : v = 0
  · subst hv
    exact ⟨0, tendsto_const_nhds.congr (fun t => (H_zero hF t).symm)⟩
  · have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
    have hu : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    obtain ⟨L, hL⟩ := exists_lim_unit hF hu
    have hvu : ‖v‖ • (‖v‖⁻¹ • v) = v := by
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    refine ⟨‖v‖ • L, ?_⟩
    have := tendsto_H_smul hn hL
    rwa [hvu] at this

/-- The candidate linear isometry: the norm limit of the difference quotients. -/
noncomputable def T (F : X → Y) (v : X) : Y := limUnder (𝓝[>] (0 : ℝ)) (H F v)

lemma tendsto_T [CompleteSpace Y] (hF : Good F) (v : X) :
    Tendsto (H F v) (𝓝[>] 0) (𝓝 (T F v)) :=
  tendsto_nhds_limUnder (exists_lim hF v)

variable [CompleteSpace Y]

lemma T_smul_pos (hF : Good F) {c : ℝ} (hc : 0 < c) (v : X) : T F (c • v) = c • T F v :=
  tendsto_nhds_unique (tendsto_T hF (c • v)) (tendsto_H_smul hc (tendsto_T hF v))

lemma T_zero (hF : Good F) : T F 0 = 0 :=
  tendsto_nhds_unique ((tendsto_T hF 0).congr (H_zero hF)) tendsto_const_nhds

lemma T_neg_unit (hF : Good F) {u : X} (hu : ‖u‖ = 1) : T F (-u) = -T F u := by
  have h1 : Tendsto (fun t => H F u t + H F (-u) t) (𝓝[>] 0) (𝓝 (T F u + T F (-u))) :=
    (tendsto_T hF u).add (tendsto_T hF (-u))
  have h2 : Tendsto (fun t => H F u t + H F (-u) t) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_mul_zero 16)
    filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    exact H_add_neg_unit hF hu ht.1 ht.2.le
  have h3 := tendsto_nhds_unique h1 h2
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h3

lemma T_neg (hF : Good F) (v : X) : T F (-v) = -T F v := by
  by_cases hv : v = 0
  · subst hv
    rw [neg_zero, T_zero hF, neg_zero]
  · have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
    have hu : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hvu : ‖v‖ • (‖v‖⁻¹ • v) = v := by
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    calc T F (-v) = T F (‖v‖ • -(‖v‖⁻¹ • v)) := by rw [smul_neg, hvu]
      _ = ‖v‖ • -T F (‖v‖⁻¹ • v) := by rw [T_smul_pos hF hn, T_neg_unit hF hu]
      _ = -T F (‖v‖ • (‖v‖⁻¹ • v)) := by rw [T_smul_pos hF hn, smul_neg]
      _ = -T F v := by rw [hvu]

lemma T_smul (hF : Good F) (c : ℝ) (v : X) : T F (c • v) = c • T F v := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have hc' : 0 < -c := neg_pos.2 hc
    calc T F (c • v) = T F ((-c) • -v) := by rw [neg_smul_neg]
      _ = c • T F v := by rw [T_smul_pos hF hc', T_neg hF, neg_smul_neg]
  · rw [zero_smul, zero_smul, T_zero hF]
  · exact T_smul_pos hF hc v

lemma T_norm (hF : Good F) (v : X) : ‖T F v‖ = ‖v‖ := by
  have hpos : 0 < ‖v‖ + 1 := by positivity
  have hev : (fun _ : ℝ => ‖v‖) =ᶠ[𝓝[>] 0] fun t => ‖H F v t‖ := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / (‖v‖ + 1) by positivity)] with t ht
    have ht1 : t * (‖v‖ + 1) < 1 := (lt_div_iff₀ hpos).1 ht.2
    have hsmall : ‖t • v‖ ≤ 1 := by
      rw [norm_smul, Real.norm_of_nonneg ht.1.le]
      nlinarith [ht.1, norm_nonneg v]
    rw [H, norm_smul, hF.norm _ hsmall, norm_smul, norm_inv, Real.norm_of_nonneg ht.1.le,
      ← mul_assoc, inv_mul_cancel₀ ht.1.ne', one_mul]
  exact tendsto_nhds_unique (tendsto_T hF v).norm (tendsto_const_nhds.congr' hev)

lemma T_add_small (hF : Good F) {v w : X} (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    T F (v + w) = T F v + T F w := by
  have h1 : Tendsto (fun t => H F v t + H F w t + H F (-(v + w)) t) (𝓝[>] 0)
      (𝓝 (T F v + T F w + T F (-(v + w)))) :=
    ((tendsto_T hF v).add (tendsto_T hF w)).add (tendsto_T hF (-(v + w)))
  have h2 : Tendsto (fun t => H F v t + H F w t + H F (-(v + w)) t) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_mul_zero 96)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with t ht
    have hD := hF.two v w hv hw t ht.1 ht.2.le
    have e : H F v t + H F w t + H F (-(v + w)) t
        = t⁻¹ • (F (t • v) + F (t • w) + F (-(t • (v + w)))) := by
      rw [H_neg]; simp only [H, smul_add]
    rw [e, norm_smul, norm_inv, Real.norm_of_nonneg ht.1.le]
    calc t⁻¹ * ‖F (t • v) + F (t • w) + F (-(t • (v + w)))‖ ≤ t⁻¹ * (96 * t ^ 2) :=
          mul_le_mul_of_nonneg_left hD (inv_nonneg.2 ht.1.le)
      _ = 96 * t := by field_simp
  have h3 := tendsto_nhds_unique h1 h2
  rw [T_neg hF, add_neg_eq_zero] at h3
  exact h3.symm

lemma T_add (hF : Good F) (v w : X) : T F (v + w) = T F v + T F w := by
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = ‖v‖ + ‖w‖ + 1 := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hc_def]; positivity
  have key : ∀ z : X, c • (c⁻¹ • z) = z := fun z => by
    rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hsmall : ∀ z : X, ‖z‖ ≤ c → ‖c⁻¹ • z‖ ≤ 1 := fun z hz => by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hc.le, inv_mul_le_iff₀ hc, mul_one]
    exact hz
  have hv' := hsmall v (by rw [hc_def]; linarith [norm_nonneg w])
  have hw' := hsmall w (by rw [hc_def]; linarith [norm_nonneg v])
  calc T F (v + w) = T F (c • (c⁻¹ • v + c⁻¹ • w)) := by rw [smul_add, key, key]
    _ = c • (T F (c⁻¹ • v) + T F (c⁻¹ • w)) := by rw [T_smul_pos hF hc, T_add_small hF hv' hw']
    _ = T F (c • (c⁻¹ • v)) + T F (c • (c⁻¹ • w)) := by
        rw [smul_add, T_smul_pos hF hc, T_smul_pos hF hc]
    _ = T F v + T F w := by rw [key, key]

lemma bound_unit (hF : Good F) {u : X} (hu : ‖u‖ = 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ‖H F u t - T F u‖ ≤ 8 * t := by
  have h1 : Tendsto (fun s => ‖H F u t - H F u s‖) (𝓝[>] 0) (𝓝 ‖H F u t - T F u‖) :=
    (tendsto_const_nhds.sub (tendsto_T hF u)).norm
  have h2 : Tendsto (fun s : ℝ => 8 * t + 24 * s) (𝓝[>] 0) (𝓝 (8 * t)) := by
    simpa using (tendsto_const_mul_zero 24).const_add (8 * t)
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with s hs
  exact H_sub_unit hF hu ht0 ht1 hs.1 hs.2.le

lemma bound (hF : Good F) {x : X} (hx : ‖x‖ ≤ 1) : ‖F x - T F x‖ ≤ 8 * ‖x‖ ^ 2 := by
  by_cases hx0 : x = 0
  · subst hx0
    simp [hF.zero, T_zero hF]
  · have hr : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hu : ‖‖x‖⁻¹ • x‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
    have hxu : ‖x‖ • (‖x‖⁻¹ • x) = x := by
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hFx : F x = ‖x‖ • H F (‖x‖⁻¹ • x) ‖x‖ := by
      rw [H, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, hxu]
    have hTx : T F x = ‖x‖ • T F (‖x‖⁻¹ • x) := by
      rw [← T_smul_pos hF hr, hxu]
    rw [hFx, hTx, ← smul_sub, norm_smul, norm_norm]
    calc ‖x‖ * ‖H F (‖x‖⁻¹ • x) ‖x‖ - T F (‖x‖⁻¹ • x)‖ ≤ ‖x‖ * (8 * ‖x‖) :=
          mul_le_mul_of_nonneg_left (bound_unit hF hu hr hx) hr.le
      _ = 8 * ‖x‖ ^ 2 := by ring

/-- `T` packaged as a linear isometry. -/
noncomputable def Tiso (hF : Good F) : X →ₗᵢ[ℝ] Y where
  toFun := T F
  map_add' := T_add hF
  map_smul' := fun c v => T_smul hF c v
  norm_map' := T_norm hF

end Sol_Plasticity_U16_linearize

theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (F : X → Y)
    (hmaps : Set.MapsTo F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (hcover : Metric.sphere (0 : Y) 1 ⊆ F '' Metric.closedBall (0 : X) 1) :
    ∃ T : X →ₗᵢ[ℝ] Y, ∀ x ∈ Metric.closedBall (0 : X) 1, ‖F x - T x‖ ≤ 8 * ‖x‖ ^ 2 := by
  have hne := Plasticity.U16.norm_eq F hmaps hlip hsphere hcover
  have hF : Sol_Plasticity_U16_linearize.Good F :=
    { zero := hne.1
      norm := fun x hx => hne.2 x (mem_closedBall_zero_iff.2 hx)
      mixed := fun v hv t u ht0 ht1 hu0 hu1 =>
        Plasticity.U16.mixed_scale F hmaps hlip hsphere hcover v hv t u ht0 ht1 hu0 hu1
      two := fun v w hv hw t ht0 ht1 =>
        Plasticity.U16.two_direction F hmaps hlip hsphere hcover v w hv hw t ht0 ht1 }
  exact ⟨Sol_Plasticity_U16_linearize.Tiso hF,
    fun x hx => Sol_Plasticity_U16_linearize.bound hF (mem_closedBall_zero_iff.1 hx)⟩
