-- Prove2me | solution 1 for RockafellarMaxMono.Cyclic.dirDeriv_eq_max_subdiff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:56:24.782534+00:00
-- url     : https://prove2.me/submissions/aed4ba84-1047-4f6b-a0e9-0a63cd3fad71

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
open Filter Topology
open Filter Topology Set

namespace RockafellarMaxMono.Cyclic

section Core
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def rqq (h : V → ℝ) (x u : V) (t : ℝ) : ℝ := (h (x + t • u) - h x) / t

lemma rqq_mono (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (x u : V) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) : rqq h x u s ≤ rqq h x u t := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have key : h (x + s • u) ≤ (1 - s / t) * h x + (s / t) * h (x + t • u) := by
    have e : x + s • u = (1 - s / t) • x + (s / t) • (x + t • u) := by
      rw [smul_add, smul_smul, div_mul_cancel₀ _ ht.ne']
      rw [sub_smul, one_smul]; abel
    rw [e]
    have := hconv.2 (Set.mem_univ x) (Set.mem_univ (x + t • u))
      (sub_nonneg.2 ((div_le_one ht).2 hst)) (div_nonneg hs.le ht.le) (by ring)
    simpa [smul_eq_mul] using this
  unfold rqq
  rw [div_le_div_iff₀ hs ht]
  have h1 : (s / t) * t = s := div_mul_cancel₀ _ ht.ne'
  have h2 : (h (x + s • u) - h x) ≤ (s / t) * (h (x + t • u) - h x) := by linarith
  have h3 : (h (x + s • u) - h x) * t ≤ (s / t) * (h (x + t • u) - h x) * t :=
    mul_le_mul_of_nonneg_right h2 ht.le
  calc (h (x + s • u) - h x) * t ≤ (s / t) * (h (x + t • u) - h x) * t := h3
    _ = (h (x + t • u) - h x) * s := by rw [mul_comm (s/t), mul_assoc, h1]

lemma rqq_lb (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (x u : V) {t : ℝ} (ht : 0 < t) :
    h x - h (x - u) ≤ rqq h x u t := by
  have h1t : 0 < 1 + t := by linarith
  have key : h x ≤ (t / (1 + t)) * h (x - u) + (1 / (1 + t)) * h (x + t • u) := by
    have e : x = (t / (1 + t)) • (x - u) + (1 / (1 + t)) • (x + t • u) := by
      have hab : t / (1 + t) + 1 / (1 + t) = 1 := by
        rw [← add_div, div_eq_one_iff_eq h1t.ne']; ring
      have h2 : 1 / (1 + t) * t - t / (1 + t) = 0 := by ring
      calc x = (t / (1 + t) + 1 / (1 + t)) • x + (1 / (1 + t) * t - t / (1 + t)) • u := by
            rw [hab, h2]; simp
        _ = _ := by module
    conv_lhs => rw [e]
    have := hconv.2 (Set.mem_univ (x - u)) (Set.mem_univ (x + t • u))
      (div_nonneg ht.le h1t.le) (div_nonneg zero_le_one h1t.le) (by field_simp; ring)
    simpa [smul_eq_mul] using this
  unfold rqq
  rw [le_div_iff₀ ht]
  have : (1 + t) * h x ≤ t * h (x - u) + h (x + t • u) := by
    have := mul_le_mul_of_nonneg_left key h1t.le
    have e1 : (1 + t) * ((t / (1 + t)) * h (x - u) + (1 / (1 + t)) * h (x + t • u))
        = t * h (x - u) + h (x + t • u) := by field_simp
    linarith
  nlinarith

noncomputable def rpp (h : V → ℝ) (x u : V) : ℝ := sInf (rqq h x u '' Ioi 0)

lemma rpp_bdd (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (x u : V) :
    BddBelow (rqq h x u '' Ioi 0) := by
  refine ⟨h x - h (x - u), ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact rqq_lb h hconv x u ht

lemma rpp_le (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (x u : V) {t : ℝ} (ht : 0 < t) :
    rpp h x u ≤ rqq h x u t :=
  csInf_le (rpp_bdd h hconv x u) ⟨t, ht, rfl⟩

lemma le_rpp (h : V → ℝ) (x u : V) {c : ℝ} (hc : ∀ t, 0 < t → c ≤ rqq h x u t) :
    c ≤ rpp h x u := by
  apply le_csInf ((Set.nonempty_Ioi (a := (0:ℝ))).image _)
  rintro _ ⟨t, ht, rfl⟩
  exact hc t ht

lemma rqq_smul (h : V → ℝ) (x u : V) {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    rqq h x (c • u) t = c * rqq h x u (t * c) := by
  unfold rqq
  rw [smul_smul]
  field_simp

lemma rpp_hom (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (x u : V) {c : ℝ} (hc : 0 < c) :
    rpp h x (c • u) = c * rpp h x u := by
  apply le_antisymm
  · have : rpp h x (c • u) / c ≤ rpp h x u := by
      apply le_rpp
      intro t ht
      rw [div_le_iff₀ hc]
      have := rpp_le h hconv x (c • u) (t := t / c) (div_pos ht hc)
      rw [rqq_smul h x u hc (div_pos ht hc), div_mul_cancel₀ _ hc.ne'] at this
      linarith
    rw [div_le_iff₀ hc] at this; linarith
  · apply le_rpp
    intro t ht
    rw [rqq_smul h x u hc ht]
    exact mul_le_mul_of_nonneg_left (rpp_le h hconv x u (mul_pos ht hc)) hc.le

lemma rqq_add (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (x u v : V) {t : ℝ} (ht : 0 < t) :
    rqq h x (u + v) t ≤ rqq h x u (2 * t) + rqq h x v (2 * t) := by
  have key : h (x + t • (u + v)) ≤ (1/2 : ℝ) * h (x + (2 * t) • u) + (1/2 : ℝ) * h (x + (2*t) • v) := by
    have e : x + t • (u + v) = (1/2 : ℝ) • (x + (2 * t) • u) + (1/2 : ℝ) • (x + (2*t) • v) := by
      module
    rw [e]
    have := hconv.2 (Set.mem_univ (x + (2 * t) • u)) (Set.mem_univ (x + (2*t) • v))
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    simpa [smul_eq_mul] using this
  unfold rqq
  rw [← add_div, div_le_div_iff₀ ht (by linarith)]
  nlinarith

lemma rpp_add (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (x u v : V) :
    rpp h x (u + v) ≤ rpp h x u + rpp h x v := by
  have H : ∀ s s' : ℝ, 0 < s → 0 < s' → rpp h x (u + v) ≤ rqq h x u s + rqq h x v s' := by
    intro s s' hs hs'
    have hm : 0 < min s s' := lt_min hs hs'
    have a1 := rqq_mono h hconv x u hm (min_le_left s s')
    have a2 := rqq_mono h hconv x v hm (min_le_right s s')
    have a3 := rqq_add h hconv x u v (t := min s s' / 2) (by linarith)
    have a4 := rpp_le h hconv x (u + v) (t := min s s' / 2) (by linarith)
    have : 2 * (min s s' / 2) = min s s' := by ring
    rw [this] at a3
    linarith
  have H2 : ∀ s', 0 < s' → rpp h x (u + v) - rqq h x v s' ≤ rpp h x u := by
    intro s' hs'
    apply le_rpp; intro s hs; have := H s s' hs hs'; linarith
  have : rpp h x (u + v) - rpp h x u ≤ rpp h x v := by
    apply le_rpp; intro s' hs'; have := H2 s' hs'; linarith
  linarith

lemma rpp_zero (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (x : V) : rpp h x 0 = 0 := by
  have : rqq h x 0 '' Ioi 0 = {0} := by
    ext y; simp only [mem_image, mem_Ioi, mem_singleton_iff, rqq, smul_zero, add_zero, sub_self,
      zero_div]
    constructor
    · rintro ⟨_, _, rfl⟩; rfl
    · rintro rfl; exact ⟨1, one_pos, rfl⟩
  unfold rpp; rw [this, csInf_singleton]

lemma exists_sub (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (hcont : Continuous h) (x u : V) :
    ∃ g : StrongDual ℝ V, (∀ y, h x + g (y - x) ≤ h y) ∧ g u = rpp h x u := by
  set f : V →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' u (rpp h x u) (fun c hc => by
    rcases smul_eq_zero.1 hc with hc | hc
    · simp [hc]
    · subst hc; simp [rpp_zero h hconv x]) with hfdef
  have hf : ∀ z : f.domain, f z ≤ rpp h x z := by
    rintro ⟨z, hz⟩
    have hz' := hz
    rw [hfdef, LinearPMap.domain_mkSpanSingleton, Submodule.mem_span_singleton] at hz'
    obtain ⟨c, rfl⟩ := hz'
    have hfa : f ⟨c • u, hz⟩ = c * rpp h x u := LinearPMap.mkSpanSingleton'_apply _ _ _ c hz
    rw [hfa]
    show c * rpp h x u ≤ rpp h x (c • u)
    rcases lt_trichotomy c 0 with hc | hc | hc
    · have e : c • u = (-c) • (-u) := by rw [neg_smul_neg]
      rw [e, rpp_hom h hconv x _ (neg_pos.2 hc)]
      have := rpp_add h hconv x u (-u)
      rw [add_neg_cancel, rpp_zero h hconv x] at this
      nlinarith
    · subst hc; simp [rpp_zero h hconv x]
    · rw [rpp_hom h hconv x _ hc]
  obtain ⟨g, hg1, hg2⟩ := exists_extension_of_le_sublinear f (rpp h x)
    (fun c hc v => rpp_hom h hconv x v hc) (rpp_add h hconv x) hf
  have hgq : ∀ v, g v ≤ h (x + v) - h x := by
    intro v
    have := (hg2 v).trans (rpp_le h hconv x v one_pos)
    simpa [rqq] using this
  -- continuity
  obtain ⟨δ, hδ, hδh⟩ := Metric.continuousAt_iff.1 (hcont.continuousAt (x := x)) 1 one_pos
  have hb : ∀ v : V, ‖v‖ ≤ δ / 2 → g v ≤ 1 := by
    intro v hv
    have := hδh (x := x + v) (by rw [dist_eq_norm]; simp; linarith)
    rw [Real.dist_eq] at this
    have := hgq v
    have := (abs_lt.1 ‹|h (x + v) - h x| < 1›).2
    linarith
  have hδ2 : 0 < δ / 2 := by linarith
  have bound : ∀ v : V, ‖g v‖ ≤ (2 / δ) * ‖v‖ := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
    set w := ((δ / 2) / ‖v‖) • v with hw
    have hwn : ‖w‖ ≤ δ / 2 := by
      rw [hw, norm_smul, Real.norm_of_nonneg (div_nonneg hδ2.le hn.le), div_mul_cancel₀ _ hn.ne']
    have hwn' : ‖-w‖ ≤ δ / 2 := by rwa [norm_neg]
    have a1 := hb w hwn
    have a2 := hb (-w) hwn'
    rw [map_neg] at a2
    rw [hw, map_smul, smul_eq_mul] at a1 a2
    rw [Real.norm_eq_abs, abs_le]
    have e : (2 / δ) * ‖v‖ = 1 / ((δ / 2) / ‖v‖) := by field_simp
    have hpos : 0 < (δ / 2) / ‖v‖ := div_pos hδ2 hn
    rw [e]
    constructor
    · have : -1 ≤ (δ / 2 / ‖v‖) * g v := by linarith
      calc -(1 / (δ / 2 / ‖v‖)) = (1 / (δ / 2 / ‖v‖)) * (-1) := by ring
        _ ≤ (1 / (δ / 2 / ‖v‖)) * ((δ / 2 / ‖v‖) * g v) := by gcongr
        _ = g v := by field_simp
    · rw [le_div_iff₀ hpos]; linarith
  refine ⟨g.mkContinuous (2 / δ) bound, ?_, ?_⟩
  · intro y
    rw [LinearMap.mkContinuous_apply]
    have := hgq (y - x)
    rw [add_sub_cancel] at this
    linarith
  · rw [LinearMap.mkContinuous_apply]
    have := hg1 ⟨u, Submodule.mem_span_singleton_self u⟩
    have hfa1 : f ⟨u, Submodule.mem_span_singleton_self u⟩ = rpp h x u :=
      LinearPMap.mkSpanSingleton'_apply_self _ _ _ _
    rw [this, hfa1]


lemma memiff (φ : V → ℝ) (x' : StrongDual ℝ V) (y : V) :
    x' ∈ Shared.subdiff (fun z => ((φ z : ℝ) : EReal)) y ↔ ∀ z, φ y + x' (z - y) ≤ φ z := by
  simp only [Shared.subdiff, Set.mem_setOf_eq, ← EReal.coe_add, EReal.coe_le_coe_iff]

lemma sub_le_rpp (h : V → ℝ) (x u : V) (x' : StrongDual ℝ V)
    (hx' : ∀ z, h x + x' (z - x) ≤ h z) : x' u ≤ rpp h x u := by
  apply le_rpp
  intro t ht
  have := hx' (x + t • u)
  rw [add_sub_cancel_left, map_smul, smul_eq_mul] at this
  unfold rqq
  rw [le_div_iff₀ ht]; linarith

lemma sub_norm_bound (h : V → ℝ) (hcont : Continuous h) (x : V) :
    ∃ C : ℝ, ∀ x' : StrongDual ℝ V, (∀ z, h x + x' (z - x) ≤ h z) → ‖x'‖ ≤ C := by
  obtain ⟨δ, hδ, hδh⟩ := Metric.continuousAt_iff.1 (hcont.continuousAt (x := x)) 1 one_pos
  have hδ2 : 0 < δ / 2 := by linarith
  refine ⟨2 / δ, fun x' hx' => ?_⟩
  have hb : ∀ v : V, ‖v‖ ≤ δ / 2 → x' v ≤ 1 := by
    intro v hv
    have := hδh (x := x + v) (by rw [dist_eq_norm]; simp; linarith)
    rw [Real.dist_eq] at this
    have h2 := hx' (x + v)
    rw [add_sub_cancel_left] at h2
    have := (abs_lt.1 this).2
    linarith
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set w := ((δ / 2) / ‖v‖) • v with hw
  have hwn : ‖w‖ ≤ δ / 2 := by
    rw [hw, norm_smul, Real.norm_of_nonneg (div_nonneg hδ2.le hn.le), div_mul_cancel₀ _ hn.ne']
  have hwn' : ‖-w‖ ≤ δ / 2 := by rwa [norm_neg]
  have a1 := hb w hwn
  have a2 := hb (-w) hwn'
  rw [map_neg] at a2
  rw [hw, map_smul, smul_eq_mul] at a1 a2
  rw [Real.norm_eq_abs, abs_le]
  have e : (2 / δ) * ‖v‖ = 1 / ((δ / 2) / ‖v‖) := by field_simp
  have hpos : 0 < (δ / 2) / ‖v‖ := div_pos hδ2 hn
  rw [e]
  constructor
  · have : -1 ≤ (δ / 2 / ‖v‖) * x' v := by linarith
    calc -(1 / (δ / 2 / ‖v‖)) = (1 / (δ / 2 / ‖v‖)) * (-1) := by ring
      _ ≤ (1 / (δ / 2 / ‖v‖)) * ((δ / 2 / ‖v‖) * x' v) := by gcongr
      _ = x' v := by field_simp
  · rw [le_div_iff₀ hpos]; linarith

theorem dirDeriv_core (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (x : V) :
    (Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x).Nonempty ∧
    IsCompact (StrongDual.toWeakDual '' Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x) ∧
    ∀ u : V, ∃ d : ℝ,
      Tendsto (fun t : ℝ => (h (x + t • u) - h x) / t) (𝓝[>] 0) (𝓝 d) ∧
      IsGreatest ((fun x' : StrongDual ℝ V => x' u) ''
        Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x) d := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨g, hg, -⟩ := exists_sub h hconv hcont x 0
    exact ⟨g, (memiff h g x).2 hg⟩
  · obtain ⟨C, hC⟩ := sub_norm_bound h hcont x
    apply WeakDual.isCompact_of_bounded_of_closed
    · rw [← WeakDual.isBounded_toWeakDual_preimage_iff_isBounded]
      apply (Metric.isBounded_closedBall (x := (0 : StrongDual ℝ V)) (r := C)).subset
      rintro w ⟨x', hx', hw⟩
      have : x' = w := hw
      subst this
      simpa using hC x' ((memiff h x' x).1 hx')
    · have e : StrongDual.toWeakDual '' Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x =
          ⋂ y : V, {w : WeakDual ℝ V | h x + w (y - x) ≤ h y} := by
        ext w
        simp only [Set.mem_image, Set.mem_iInter, Set.mem_setOf_eq]
        constructor
        · rintro ⟨x', hx', rfl⟩ y
          exact (memiff h x' x).1 hx' y
        · intro hw
          exact ⟨WeakDual.toStrongDual w, (memiff h _ x).2 hw, rfl⟩
      rw [e]
      exact isClosed_iInter fun y =>
        isClosed_le (continuous_const.add (WeakDual.eval_continuous _)) continuous_const
  · intro u
    obtain ⟨g, hg, hgu⟩ := exists_sub h hconv hcont x u
    refine ⟨rpp h x u, ?_, ⟨⟨g, (memiff h g x).2 hg, hgu⟩, ?_⟩⟩
    · rw [tendsto_order]
      constructor
      · intro a' ha'
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact lt_of_lt_of_le ha' (rpp_le h hconv x u ht)
      · intro b' hb'
        obtain ⟨_, ⟨t0, ht0, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt
          ((Set.nonempty_Ioi (a := (0:ℝ))).image _) hb'
        filter_upwards [Ioo_mem_nhdsGT ht0] with t ht
        exact lt_of_le_of_lt (rqq_mono h hconv x u ht.1 ht.2.le) hlt
    · rintro _ ⟨x', hx', rfl⟩
      exact sub_le_rpp h x u x' ((memiff h x' x).1 hx')

lemma mono_line (h k : V → ℝ)
    (hconv : ConvexOn ℝ Set.univ h) (hcont : Continuous h) (kcont : Continuous k)
    (hsub : ∀ x : V, Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x ⊆
      Shared.subdiff (fun y => ((k y : ℝ) : EReal)) x) (a d : V) :
    k a - h a ≤ k (a + d) - h (a + d) := by
  set g : ℝ → ℝ := fun t => k (a + t • d) - h (a + t • d) with hgdef
  have gc : Continuous g := by
    have c1 : Continuous fun t : ℝ => a + t • d := continuous_const.add (continuous_id.smul continuous_const)
    exact (kcont.comp c1).sub (hcont.comp c1)
  have key : ∀ ε : ℝ, 0 < ε → g 0 ≤ g 1 + ε := by
    intro ε hε
    have := image_le_of_liminf_slope_right_lt_deriv_boundary' (f := fun t => - g t) (f' := fun _ => 0)
      (a := 0) (b := 1) gc.neg.continuousOn ?_ (B := fun t => -g 0 + ε * t) (B' := fun _ => ε)
      (by simp) (by fun_prop) ?_ (fun _ _ _ => hε) (x := 1) ⟨zero_le_one, le_rfl⟩
    · have h2 : -g 1 ≤ -g 0 + ε * 1 := this
      linarith
    · intro t _ r hr
      apply Filter.Eventually.frequently
      set y := a + t • d with hy
      obtain ⟨x', hx', hx'd⟩ := exists_sub h hconv hcont y d
      have hk := (memiff k x' y).1 (hsub y ((memiff h x' y).2 hx'))
      obtain ⟨_, ⟨t0, ht0, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt
          ((Set.nonempty_Ioi (a := (0:ℝ))).image _) (show rpp h y d < rpp h y d + r by linarith)
      have ht0' : t < t + t0 := by linarith [Set.mem_Ioi.1 ht0]
      filter_upwards [Ioo_mem_nhdsGT ht0'] with z hz
      have hzt : 0 < z - t := by linarith [hz.1]
      have e : a + z • d = y + (z - t) • d := by rw [hy, sub_smul]; abel
      have q1 := rqq_mono h hconv y d (t := t0) hzt (by linarith [hz.2])
      have hk2 := hk (y + (z - t) • d)
      rw [add_sub_cancel_left, map_smul, smul_eq_mul] at hk2
      unfold rqq at q1
      rw [div_le_iff₀ hzt] at q1
      rw [slope_def_field]
      simp only [hgdef, e]
      rw [← hy, div_lt_iff₀ hzt]
      have : rqq h y d t0 * (z - t) < (rpp h y d + r) * (z - t) := mul_lt_mul_of_pos_right hlt hzt
      rw [← hx'd] at this
      unfold rqq at this
      nlinarith
    · intro t _
      have := ((hasDerivAt_id t).const_mul ε).const_add (-g 0)
      simpa using this.hasDerivWithinAt
  have h1 : g 0 ≤ g 1 := le_of_forall_pos_le_add key
  simpa [hgdef] using h1

theorem finite_core {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] (h k : V → ℝ)
    (hconv : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (kconv : ConvexOn ℝ Set.univ k) (kcont : Continuous k)
    (hsub : ∀ x : V, Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x ⊆
      Shared.subdiff (fun y => ((k y : ℝ) : EReal)) x) :
    ∃ c : ℝ, ∀ x : V, k x = h x + c := by
  refine ⟨k 0 - h 0, fun x => ?_⟩
  have a1 := mono_line h k hconv hcont kcont hsub 0 x
  have a2 := mono_line h k hconv hcont kcont hsub x (-x)
  simp only [zero_add, add_neg_cancel] at a1 a2
  linarith

end Core
end RockafellarMaxMono.Cyclic

open RockafellarMaxMono.Cyclic
open RockafellarMaxMono

theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (x : V) :
    (Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x).Nonempty ∧
    IsCompact (StrongDual.toWeakDual '' Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x) ∧
    ∀ u : V, ∃ d : ℝ,
      Tendsto (fun t : ℝ => (h (x + t • u) - h x) / t) (𝓝[>] 0) (𝓝 d) ∧
      IsGreatest ((fun x' : StrongDual ℝ V => x' u) ''
        Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x) d := by
  exact dirDeriv_core h hconv hcont x
