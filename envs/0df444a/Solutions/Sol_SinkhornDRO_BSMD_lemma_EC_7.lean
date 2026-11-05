-- Prove2me | solution 1 for SinkhornDRO.BSMD.lemma_EC_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T06:42:21.221379+00:00
-- url     : https://prove2.me/submissions/42cc7959-8711-464a-9f52-cc1468ea4ad0

import Mathlib
import Definitions.Def_SinkhornDRO_BSMD_MirrorSetup

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace Topology

namespace Aux_BSMD7
open SinkhornDRO.BSMD

lemma N_zero {d : ℕ} (𝒩 : MirrorNorm d) : 𝒩.N 0 = 0 := by
  have := 𝒩.smul_eq 0 0
  simpa using this

lemma inner_le_of_N {d : ℕ} (𝒩 : MirrorNorm d) (y x : Param d) (hx : 𝒩.N x ≤ 1) :
    ⟪y, x⟫ ≤ ‖y‖ / 𝒩.c := by
  have h1 := 𝒩.lower x
  have hc := 𝒩.c_pos
  have hx' : ‖x‖ ≤ 1 / 𝒩.c := by rw [le_div_iff₀ hc]; linarith
  calc ⟪y, x⟫ ≤ ‖y‖ * ‖x‖ := real_inner_le_norm _ _
    _ ≤ ‖y‖ * (1 / 𝒩.c) := by gcongr
    _ = ‖y‖ / 𝒩.c := by ring

lemma dual_bdd {d : ℕ} (𝒩 : MirrorNorm d) (y : Param d) :
    BddAbove (Set.range fun x : {x : Param d // 𝒩.N x ≤ 1} => ⟪y, (x : Param d)⟫) := by
  refine ⟨‖y‖ / 𝒩.c, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact inner_le_of_N 𝒩 y x x.2

instance unitBall_nonempty {d : ℕ} (𝒩 : MirrorNorm d) : Nonempty {x : Param d // 𝒩.N x ≤ 1} :=
  ⟨⟨0, by rw [N_zero]; norm_num⟩⟩

lemma dual_le {d : ℕ} (𝒩 : MirrorNorm d) (y : Param d) : dualNorm 𝒩 y ≤ ‖y‖ / 𝒩.c :=
  ciSup_le fun x => inner_le_of_N 𝒩 y x x.2

lemma dual_nonneg {d : ℕ} (𝒩 : MirrorNorm d) (y : Param d) : 0 ≤ dualNorm 𝒩 y := by
  have := le_ciSup (dual_bdd 𝒩 y) ⟨0, by rw [N_zero]; norm_num⟩
  rw [show (0:ℝ) = ⟪y, (0:Param d)⟫ by simp]
  exact this

lemma dual_sq_le {d : ℕ} (𝒩 : MirrorNorm d) (y : Param d) :
    dualNorm 𝒩 y ^ 2 ≤ (𝒩.c ^ 2)⁻¹ * ‖y‖ ^ 2 := by
  have h1 := dual_le 𝒩 y
  have h0 := dual_nonneg 𝒩 y
  have hc := 𝒩.c_pos
  calc dualNorm 𝒩 y ^ 2 ≤ (‖y‖ / 𝒩.c) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = (𝒩.c ^ 2)⁻¹ * ‖y‖ ^ 2 := by field_simp

lemma dual_lip {d : ℕ} (𝒩 : MirrorNorm d) : Continuous (dualNorm 𝒩) := by
  refine (LipschitzWith.of_le_add_mul' (1 / 𝒩.c) (fun y1 y2 => ?_)).continuous
  refine ciSup_le fun x => ?_
  have h1 : ⟪y2, (x : Param d)⟫ ≤ dualNorm 𝒩 y2 := le_ciSup (dual_bdd 𝒩 y2) x
  have h2 := inner_le_of_N 𝒩 (y1 - y2) x x.2
  rw [inner_sub_left] at h2
  rw [dist_eq_norm]
  have : ‖y1 - y2‖ / 𝒩.c = 1 / 𝒩.c * ‖y1 - y2‖ := by ring
  linarith


lemma N_nonneg {d : ℕ} (𝒩 : MirrorNorm d) (x : Param d) : 0 ≤ 𝒩.N x :=
  le_trans (mul_nonneg 𝒩.c_pos.le (norm_nonneg x)) (𝒩.lower x)

lemma N_neg {d : ℕ} (𝒩 : MirrorNorm d) (x : Param d) : 𝒩.N (-x) = 𝒩.N x := by
  have := 𝒩.smul_eq (-1) x
  simpa using this

lemma N_sub_comm {d : ℕ} (𝒩 : MirrorNorm d) (x y : Param d) : 𝒩.N (x - y) = 𝒩.N (y - x) := by
  rw [← N_neg, neg_sub]

lemma inner_le_dual_mul {d : ℕ} (𝒩 : MirrorNorm d) (y x : Param d) :
    ⟪y, x⟫ ≤ dualNorm 𝒩 y * 𝒩.N x := by
  rcases eq_or_lt_of_le (N_nonneg 𝒩 x) with h0 | hpos
  · have : ‖x‖ = 0 := by
      have := 𝒩.lower x
      rw [← h0] at this
      exact le_antisymm (by nlinarith [𝒩.c_pos, norm_nonneg x]) (norm_nonneg x)
    rw [norm_eq_zero] at this
    subst this
    rw [N_zero, mul_zero, inner_zero_right]
  · set x' := (𝒩.N x)⁻¹ • x with hx'
    have hN : 𝒩.N x' ≤ 1 := by
      rw [hx', 𝒩.smul_eq, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
    have h1 : ⟪y, x'⟫ ≤ dualNorm 𝒩 y := le_ciSup (dual_bdd 𝒩 y) ⟨x', hN⟩
    have h2 : ⟪y, x⟫ = 𝒩.N x * ⟪y, x'⟫ := by
      rw [hx', real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    rw [h2, mul_comm (dualNorm 𝒩 y)]
    exact mul_le_mul_of_nonneg_left h1 hpos.le

lemma path_deriv {d : ℕ} (Θ : Set (Param d)) (hΘv : Convex ℝ Θ) (ω : Param d → ℝ)
    (ω' : Param d → Param d) (hgrad : ∀ θ ∈ Θ, HasGradientWithinAt ω (ω' θ) Θ θ)
    (a b : Param d) (ha : a ∈ Θ) (hb : b ∈ Θ) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun s : ℝ => ω (a + s • (b - a))) ⟪ω' (a + s • (b - a)), b - a⟫
      (Icc 0 1) s := by
  have hmem : ∀ s ∈ Icc (0:ℝ) 1, a + s • (b - a) ∈ Θ := fun s hs => hΘv.add_smul_sub_mem ha hb hs
  have hp : HasDerivWithinAt (fun s : ℝ => a + s • (b - a)) (b - a) (Icc 0 1) s := by
    simpa using (((hasDerivAt_id s).smul_const (b - a)).const_add a).hasDerivWithinAt
  have hg := hgrad _ (hmem s hs)
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt] at hg
  have := hg.comp_hasDerivWithinAt (x := s) hp (fun s hs => hmem s hs)
  exact this

lemma bregman_lower {d : ℕ} (Θ : Set (Param d)) (hΘv : Convex ℝ Θ) (𝒩 : MirrorNorm d) (κ : ℝ)
    (ω : Param d → ℝ) (ω' : Param d → Param d) (hω : IsDistGen Θ 𝒩 κ ω ω')
    (θ θ' : Param d) (hθ : θ ∈ Θ) (hθ' : θ' ∈ Θ) :
    κ / 2 * 𝒩.N (θ' - θ) ^ 2 ≤ bregman ω ω' θ θ' := by
  obtain ⟨hgrad, -, hκ, hmono⟩ := hω
  set w := θ' - θ with hw
  set a := ⟪ω' θ, w⟫ with ha
  set c := κ / 2 * 𝒩.N w ^ 2 with hc
  let ψ : ℝ → ℝ := fun s => ω (θ + s • w) - s * a - c * s ^ 2
  have hder : ∀ s ∈ Icc (0:ℝ) 1, HasDerivWithinAt ψ
      (⟪ω' (θ + s • w), w⟫ - a - c * (2 * s)) (Icc 0 1) s := by
    intro s hs
    have h1 := path_deriv Θ hΘv ω ω' hgrad θ θ' hθ hθ' s hs
    have h2 : HasDerivWithinAt (fun s : ℝ => s * a) a (Icc 0 1) s := by
      simpa using ((hasDerivAt_id s).mul_const a).hasDerivWithinAt
    have h3 : HasDerivWithinAt (fun s : ℝ => c * s ^ 2) (c * (2 * s)) (Icc 0 1) s := by
      have := ((hasDerivAt_pow 2 s).const_mul c).hasDerivWithinAt (s := Icc 0 1)
      simpa using this
    exact (h1.sub h2).sub h3
  have hmon : MonotoneOn ψ (Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (f' := fun s => ⟪ω' (θ + s • w), w⟫ - a - c * (2 * s))
      (fun s hs => (hder s hs).continuousWithinAt) (fun s hs => ?_) (fun s hs => ?_)
    · have hs' : s ∈ Ioo (0:ℝ) 1 := by rwa [interior_Icc] at hs
      exact (hder s (Ioo_subset_Icc_self hs')).mono interior_subset
    · have hs' : s ∈ Ioo (0:ℝ) 1 := by rwa [interior_Icc] at hs
      have hm := hmono θ hθ (θ + s • w) (hΘv.add_smul_sub_mem hθ hθ' (Ioo_subset_Icc_self hs'))
      rw [add_sub_cancel_left, 𝒩.smul_eq, real_inner_smul_left, abs_of_pos hs'.1] at hm
      have hkey : κ * s * 𝒩.N w ^ 2 ≤ ⟪w, ω' (θ + s • w) - ω' θ⟫ := by
        have h' : s * (κ * s * 𝒩.N w ^ 2) ≤ s * ⟪w, ω' (θ + s • w) - ω' θ⟫ := by nlinarith
        exact le_of_mul_le_mul_left h' hs'.1
      rw [inner_sub_right, real_inner_comm (ω' (θ + s • w)) w, real_inner_comm (ω' θ) w] at hkey
      simp only [hc, ha]
      nlinarith
  have := hmon ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  simp only [ψ, zero_smul, add_zero, zero_mul, sub_zero, one_smul, one_mul, one_pow] at this
  unfold bregman
  rw [show θ + w = θ' by simp [hw]] at this
  linarith

lemma prox_three_point {d : ℕ} (Θ : Set (Param d)) (hΘv : Convex ℝ Θ) (𝒩 : MirrorNorm d)
    (κ : ℝ) (ω : Param d → ℝ) (ω' : Param d → Param d) (hω : IsDistGen Θ 𝒩 κ ω ω')
    (prox : Param d → Param d → Param d) (hprox : IsProxMap Θ ω ω' prox)
    (θ : Param d) (hθ : θ ∈ Θ) (y u : Param d) (hu : u ∈ Θ) :
    ⟪y, prox θ y - u⟫ ≤ bregman ω ω' θ u - bregman ω ω' (prox θ y) u
      - bregman ω ω' θ (prox θ y) := by
  obtain ⟨hp, hmin⟩ := hprox θ hθ y
  set p := prox θ y with hpdef
  set w := u - p with hw
  have hfo : 0 ≤ ⟪y, w⟫ - ⟪ω' θ, w⟫ + ⟪ω' p, w⟫ := by
    let k : ℝ → ℝ := fun s => s * (⟪y, w⟫ - ⟪ω' θ, w⟫) + ω (p + s • w)
    have hk : ∀ s ∈ Icc (0:ℝ) 1, k 0 ≤ k s := by
      intro s hs
      have := hmin (p + s • w) (hΘv.add_smul_sub_mem hp hu hs)
      unfold bregman at this
      simp only [k, zero_mul, zero_smul, add_zero, zero_add]
      have e1 : p + s • w - θ = (p - θ) + s • w := by abel
      rw [e1, inner_add_right, inner_add_right, real_inner_smul_right,
        real_inner_smul_right] at this
      linarith
    have hd : HasDerivWithinAt k ((⟪y, w⟫ - ⟪ω' θ, w⟫) + ⟪ω' p, w⟫) (Icc 0 1) 0 := by
      have h1 := path_deriv Θ hΘv ω ω' hω.1 p u hp hu 0 ⟨le_refl _, zero_le_one⟩
      simp only [zero_smul, add_zero] at h1
      have h2 : HasDerivWithinAt (fun s : ℝ => s * (⟪y, w⟫ - ⟪ω' θ, w⟫))
          (⟪y, w⟫ - ⟪ω' θ, w⟫) (Icc 0 1) 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).mul_const (⟪y, w⟫ - ⟪ω' θ, w⟫)).hasDerivWithinAt
      exact h2.add h1
    rw [hasDerivWithinAt_iff_tendsto_slope] at hd
    have hset : Icc (0:ℝ) 1 \ {0} = Ioc 0 1 := by
      ext s; simp only [mem_diff, mem_Icc, mem_singleton_iff, mem_Ioc]
      constructor
      · rintro ⟨⟨h0, h1⟩, hne⟩; exact ⟨lt_of_le_of_ne h0 (Ne.symm hne), h1⟩
      · rintro ⟨h0, h1⟩; exact ⟨⟨h0.le, h1⟩, h0.ne'⟩
    rw [hset] at hd
    haveI : (𝓝[Ioc (0:ℝ) 1] (0:ℝ)).NeBot := left_nhdsWithin_Ioc_neBot zero_lt_one
    have hev : ∀ᶠ s in 𝓝[Ioc (0:ℝ) 1] (0:ℝ), 0 ≤ slope k 0 s := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [slope_def_field]
      exact div_nonneg (by linarith [hk s ⟨hs.1.le, hs.2⟩]) (by linarith [hs.1])
    have := ge_of_tendsto hd hev
    linarith
  unfold bregman
  have e2 : u - θ = w + (p - θ) := by rw [hw]; abel
  have e3 : p - u = -w := by rw [hw]; abel
  rw [e2, e3, inner_add_right, inner_neg_right]
  linarith

lemma one_step {d : ℕ} (Θ : Set (Param d)) (hΘv : Convex ℝ Θ) (𝒩 : MirrorNorm d)
    (κ : ℝ) (ω : Param d → ℝ) (ω' : Param d → Param d) (hω : IsDistGen Θ 𝒩 κ ω ω')
    (prox : Param d → Param d → Param d) (hprox : IsProxMap Θ ω ω' prox)
    (θ : Param d) (hθ : θ ∈ Θ) (u : Param d) (hu : u ∈ Θ) (h : ℝ) (hh : 0 ≤ h) (v : Param d) :
    h * ⟪v, θ - u⟫ ≤ bregman ω ω' θ u - bregman ω ω' (prox θ (h • v)) u
      + h ^ 2 * dualNorm 𝒩 v ^ 2 / (2 * κ) := by
  have hκ : 0 < κ := hω.2.2.1
  have hp := (hprox θ hθ (h • v)).1
  set p := prox θ (h • v) with hpdef
  have h3 := prox_three_point Θ hΘv 𝒩 κ ω ω' hω prox hprox θ hθ (h • v) u hu
  rw [← hpdef, real_inner_smul_left] at h3
  have h4 := bregman_lower Θ hΘv 𝒩 κ ω ω' hω θ p hθ hp
  have h5 := inner_le_dual_mul 𝒩 v (θ - p)
  rw [N_sub_comm] at h5
  have e : ⟪v, θ - u⟫ = ⟪v, θ - p⟫ + ⟪v, p - u⟫ := by
    rw [← inner_add_right]; congr 1; abel
  set N := 𝒩.N (p - θ)
  set q := dualNorm 𝒩 v
  have hq : 0 ≤ q := dual_nonneg 𝒩 v
  have hN : 0 ≤ N := N_nonneg 𝒩 _
  have hamgm : h * q * N ≤ κ / 2 * N ^ 2 + h ^ 2 * q ^ 2 / (2 * κ) := by
    have key : κ / 2 * N ^ 2 + h ^ 2 * q ^ 2 / (2 * κ) - h * q * N
        = (κ * N - h * q) ^ 2 / (2 * κ) := by field_simp; ring
    have := div_nonneg (sq_nonneg (κ * N - h * q)) (by positivity : (0:ℝ) ≤ 2 * κ)
    linarith
  rw [e, mul_add]
  have : h * ⟪v, θ - p⟫ ≤ h * (q * N) := mul_le_mul_of_nonneg_left h5 hh
  nlinarith

lemma step_le {d : ℕ} (Θ : Set (Param d)) (hΘv : Convex ℝ Θ) (𝒩 : MirrorNorm d)
    (κ : ℝ) (ω : Param d → ℝ) (ω' : Param d → Param d) (hω : IsDistGen Θ 𝒩 κ ω ω')
    (prox : Param d → Param d → Param d) (hprox : IsProxMap Θ ω ω' prox)
    (θ : Param d) (hθ : θ ∈ Θ) (h : ℝ) (hh : 0 ≤ h) (v : Param d) :
    κ * 𝒩.N (prox θ (h • v) - θ) ≤ h * dualNorm 𝒩 v := by
  have hκ : 0 < κ := hω.2.2.1
  have hp := (hprox θ hθ (h • v)).1
  set p := prox θ (h • v) with hpdef
  have h3 := prox_three_point Θ hΘv 𝒩 κ ω ω' hω prox hprox θ hθ (h • v) θ hθ
  rw [← hpdef, real_inner_smul_left] at h3
  have hm := hω.2.2.2 θ hθ p hp
  have hsum : bregman ω ω' p θ + bregman ω ω' θ p = ⟪p - θ, ω' p - ω' θ⟫ := by
    unfold bregman
    simp only [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  have hzero : bregman ω ω' θ θ = 0 := by unfold bregman; simp
  have h5 := inner_le_dual_mul 𝒩 v (θ - p)
  rw [N_sub_comm] at h5
  have e : ⟪v, p - θ⟫ = -⟪v, θ - p⟫ := by rw [← inner_neg_right, neg_sub]
  rw [e] at h3
  set N := 𝒩.N (p - θ)
  set q := dualNorm 𝒩 v
  have hq : 0 ≤ q := dual_nonneg 𝒩 v
  have hN : 0 ≤ N := N_nonneg 𝒩 _
  have hk : κ * N ^ 2 ≤ h * (q * N) := by
    have : h * ⟪v, θ - p⟫ ≤ h * (q * N) := mul_le_mul_of_nonneg_left h5 hh
    nlinarith
  rcases eq_or_lt_of_le hN with h0 | hpos
  · rw [← h0]; simp; exact mul_nonneg hh hq
  · have : κ * N * N ≤ h * q * N := by nlinarith
    exact le_of_mul_le_mul_right this hpos

lemma update_mp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : ℕ} (t : Fin T) :
    ((Measure.pi fun _ : Fin T => μ).prod μ).map
        (fun p : (Fin T → Ω) × Ω => Function.update p.1 t p.2)
      = Measure.pi fun _ : Fin T => μ := by
  classical
  have hU : Measurable (fun p : (Fin T → Ω) × Ω => Function.update p.1 t p.2) :=
    measurable_update'
  refine (Measure.pi_eq (fun S hS => ?_)).symm
  rw [Measure.map_apply hU (MeasurableSet.univ_pi hS)]
  have hpre : (fun p : (Fin T → Ω) × Ω => Function.update p.1 t p.2) ⁻¹' (Set.univ.pi S)
      = (Set.univ.pi (Function.update S t Set.univ)) ×ˢ S t := by
    ext ⟨ξ, s⟩
    simp only [mem_preimage, mem_univ_pi, mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h t⟩
      by_cases hj : j = t
      · subst hj; simp
      · have := h j
        rw [Function.update_of_ne hj] at this ⊢
        exact this
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = t
      · subst hj; simpa using h2
      · have := h1 j
        rw [Function.update_of_ne hj] at this ⊢
        exact this
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => μ (S j)) (Finset.mem_univ t),
    ← Finset.mul_prod_erase Finset.univ (fun j => μ (Function.update S t Set.univ j))
      (Finset.mem_univ t)]
  simp only [Function.update_self, measure_univ, one_mul]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma lintegral_resample {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : ℕ} (t : Fin T) (H : (Fin T → Ω) → Ω → ENNReal) (hH : Measurable (Function.uncurry H))
    (hinv : ∀ ξ s s', H (Function.update ξ t s') s = H ξ s) :
    ∫⁻ ξ, H ξ (ξ t) ∂(Measure.pi fun _ : Fin T => μ)
      = ∫⁻ ξ, ∫⁻ s, H ξ s ∂μ ∂(Measure.pi fun _ : Fin T => μ) := by
  classical
  have hU : Measurable (fun p : (Fin T → Ω) × Ω => Function.update p.1 t p.2) :=
    measurable_update'
  have hG : Measurable (fun ξ : Fin T → Ω => H ξ (ξ t)) :=
    hH.comp (measurable_id.prodMk (measurable_pi_apply t))
  conv_lhs => rw [← update_mp μ t]
  rw [lintegral_map hG hU]
  have : ∀ p : (Fin T → Ω) × Ω,
      H (Function.update p.1 t p.2) ((Function.update p.1 t p.2) t) = Function.uncurry H p := by
    intro p; rw [Function.update_self, hinv]; rfl
  simp_rw [this]
  exact lintegral_prod _ hH.aemeasurable

lemma integral_resample {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : ℕ} (t : Fin T) (H : (Fin T → Ω) → Ω → ℝ) (hH : Measurable (Function.uncurry H))
    (hinv : ∀ ξ s s', H (Function.update ξ t s') s = H ξ s)
    (hint : Integrable (fun ξ => H ξ (ξ t)) (Measure.pi fun _ : Fin T => μ)) :
    ∫ ξ, H ξ (ξ t) ∂(Measure.pi fun _ : Fin T => μ)
      = ∫ ξ, ∫ s, H ξ s ∂μ ∂(Measure.pi fun _ : Fin T => μ) := by
  classical
  have hU : Measurable (fun p : (Fin T → Ω) × Ω => Function.update p.1 t p.2) :=
    measurable_update'
  have hG : Measurable (fun ξ : Fin T → Ω => H ξ (ξ t)) :=
    hH.comp (measurable_id.prodMk (measurable_pi_apply t))
  have heq : ∀ p : (Fin T → Ω) × Ω,
      H (Function.update p.1 t p.2) ((Function.update p.1 t p.2) t) = Function.uncurry H p := by
    intro p; rw [Function.update_self, hinv]; rfl
  have hint2 : Integrable (Function.uncurry H) ((Measure.pi fun _ : Fin T => μ).prod μ) := by
    have h1 := hint
    rw [← update_mp μ t, integrable_map_measure (by rw [update_mp μ t]; exact
      hG.aestronglyMeasurable) hU.aemeasurable] at h1
    exact h1.congr (Filter.Eventually.of_forall fun p => heq p)
  conv_lhs => rw [← update_mp μ t]
  rw [integral_map hU.aemeasurable (by rw [update_mp μ t]; exact hG.aestronglyMeasurable)]
  simp_rw [heq]
  exact integral_prod _ hint2

lemma iter_mem {d : ℕ} {Ω : Type*} (Θ : Set (Param d)) (ω : Param d → ℝ)
    (ω' : Param d → Param d) (prox : Param d → Param d → Param d) (hprox : IsProxMap Θ ω ω' prox)
    (v : Param d → Ω → Param d) (h : ℝ) (θ0 : Param d) (hθ0 : θ0 ∈ Θ) {T : ℕ} (ξ : Fin T → Ω) :
    ∀ t, bsmdIter prox v h θ0 ξ t ∈ Θ := by
  intro t
  induction t with
  | zero => exact hθ0
  | succ t ih =>
    simp only [bsmdIter]
    split_ifs
    · exact (hprox _ ih _).1
    · exact ih

lemma iter_meas {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (prox : Param d → Param d → Param d)
    (hprox_meas : Measurable (Function.uncurry prox))
    (v : Param d → Ω → Param d) (hv_meas : Measurable (Function.uncurry v)) (h : ℝ)
    (θ0 : Param d) {T : ℕ} :
    ∀ t, Measurable (fun ξ : Fin T → Ω => bsmdIter prox v h θ0 ξ t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    by_cases ht : t < T
    · simp only [bsmdIter, dif_pos ht]
      exact hprox_meas.comp (ih.prodMk
        ((hv_meas.comp (ih.prodMk (measurable_pi_apply _))).const_smul h))
    · simp only [bsmdIter, dif_neg ht]
      exact ih

lemma iter_indep {d : ℕ} {Ω : Type*} (prox : Param d → Param d → Param d)
    (v : Param d → Ω → Param d) (h : ℝ) (θ0 : Param d) {T : ℕ} (k : Fin T) (s : Ω) :
    ∀ t, t ≤ k.val → ∀ ξ : Fin T → Ω,
      bsmdIter prox v h θ0 (Function.update ξ k s) t = bsmdIter prox v h θ0 ξ t := by
  classical
  intro t
  induction t with
  | zero => intro _ ξ; rfl
  | succ t ih =>
    intro hk ξ
    by_cases ht : t < T
    · simp only [bsmdIter, dif_pos ht]
      have hne : (⟨t, ht⟩ : Fin T) ≠ k := by
        intro he; rw [← he] at hk; simp at hk
      rw [ih (by omega) ξ, Function.update_of_ne hne]
    · simp only [bsmdIter, dif_neg ht]
      exact ih (by omega) ξ

lemma N_eq_zero {d : ℕ} (𝒩 : MirrorNorm d) (x : Param d) (h : 𝒩.N x = 0) : x = 0 := by
  have := 𝒩.lower x
  rw [h] at this
  have : ‖x‖ = 0 := le_antisymm (by nlinarith [𝒩.c_pos, norm_nonneg x]) (norm_nonneg x)
  exact norm_eq_zero.mp this

lemma abs_inner_le_dual_mul {d : ℕ} (𝒩 : MirrorNorm d) (y x : Param d) :
    |⟪y, x⟫| ≤ dualNorm 𝒩 y * 𝒩.N x := by
  rw [abs_le]
  constructor
  · have := inner_le_dual_mul 𝒩 y (-x)
    rw [inner_neg_right, N_neg] at this; linarith
  · exact inner_le_dual_mul 𝒩 y x

lemma lint_of_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : Measurable f) (h0 : ∀ a, 0 ≤ f a) (C : ENNReal) (hC : C < ⊤)
    (hb : ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≤ C) :
    Integrable f μ ∧ ∫ a, f a ∂μ ≤ C.toReal := by
  have hfi : Integrable f μ := ⟨hf.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall h0)).mpr (lt_of_le_of_lt hb hC)⟩
  refine ⟨hfi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) hf.aestronglyMeasurable]
  exact ENNReal.toReal_mono hC.ne hb

lemma main_bound {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (Θ : Set (Param d)) (hΘv : Convex ℝ Θ)
    (𝒩 : MirrorNorm d) (κ : ℝ) (ω : Param d → ℝ) (ω' : Param d → Param d)
    (hω : IsDistGen Θ 𝒩 κ ω ω')
    (prox : Param d → Param d → Param d) (hprox : IsProxMap Θ ω ω' prox)
    (hprox_meas : Measurable (Function.uncurry prox))
    (F Fbar : Param d → ℝ) (hF_meas : Measurable F) (ΔF : ℝ)
    (hbias : ∀ θ ∈ Θ, |Fbar θ - F θ| ≤ ΔF)
    (sgbar : Param d → Param d)
    (hsgbar : ∀ θ ∈ Θ, ∀ θ' ∈ Θ, Fbar θ + ⟪sgbar θ, θ' - θ⟫ ≤ Fbar θ')
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (v : Param d → Ω → Param d) (hv_meas : Measurable (Function.uncurry v))
    (M : ℝ) (hM : 0 < M)
    (hv_int : ∀ θ ∈ Θ, Integrable (v θ) μ)
    (hv_mean : ∀ θ ∈ Θ, ∫ s, v θ s ∂μ = sgbar θ)
    (hv_sq : ∀ θ ∈ Θ, Integrable (fun s => dualNorm 𝒩 (v θ s) ^ 2) μ ∧
      ∫ s, dualNorm 𝒩 (v θ s) ^ 2 ∂μ ≤ M ^ 2)
    (θbar : Param d) (hθbar : θbar ∈ Θ ∧ ∀ θ ∈ Θ, Fbar θbar ≤ Fbar θ)
    (θstar : Param d) (hθstar : θstar ∈ Θ ∧ ∀ θ ∈ Θ, F θstar ≤ F θ)
    (θ0 : Param d) (hθ0 : θ0 ∈ Θ)
    (T : ℕ) (hT : 0 < T) (h : ℝ) (hh : 0 < h) :
    Integrable (fun ξ : Fin T → Ω => F (bsmdAvg prox v h θ0 ξ)) (Measure.pi fun _ => μ) ∧
      ∫ ξ, (F (bsmdAvg prox v h θ0 ξ) - F θstar) ∂(Measure.pi fun _ : Fin T => μ)
        ≤ 2 * ΔF + bregman ω ω' θ0 θbar / (h * T) + h * M ^ 2 / (2 * κ) := by
  classical
  have hκ : 0 < κ := hω.2.2.1
  set D := bregman ω ω' θ0 θbar with hD
  set pm := Measure.pi fun _ : Fin T => μ with hpm
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT
  set θi : ℕ → (Fin T → Ω) → Param d := fun t ξ => bsmdIter prox v h θ0 ξ t with hθi
  have hmem : ∀ t ξ, θi t ξ ∈ Θ := fun t ξ => iter_mem Θ ω ω' prox hprox v h θ0 hθ0 ξ t
  have hθm : ∀ t, Measurable (θi t) := fun t => iter_meas prox hprox_meas v hv_meas h θ0 t
  have hstep : ∀ (t : Fin T) (ξ : Fin T → Ω),
      θi (t + 1) ξ = prox (θi t ξ) (h • v (θi t ξ) (ξ t)) := by
    intro t ξ; simp only [hθi, bsmdIter, dif_pos t.isLt, Fin.eta]
  have hinvθ : ∀ (t : Fin T) (s : ℕ), s ≤ t.val → ∀ ξ s',
      θi s (Function.update ξ t s') = θi s ξ :=
    fun t s hs ξ s' => iter_indep prox v h θ0 t s' s hs ξ
  have havg : ∀ ξ : Fin T → Ω, bsmdAvg prox v h θ0 ξ = (T:ℝ)⁻¹ • ∑ t : Fin T, θi t ξ := by
    intro ξ; unfold bsmdAvg; rw [Finset.sum_range (fun t => bsmdIter prox v h θ0 ξ t)]
  -- moments of the dual norm at a fixed point
  have hdual1 : ∀ θ ∈ Θ, Integrable (fun s => dualNorm 𝒩 (v θ s)) μ ∧
      ∫ s, dualNorm 𝒩 (v θ s) ∂μ ≤ M := by
    intro θ hθ
    obtain ⟨hi2, hle2⟩ := hv_sq θ hθ
    have hm : Measurable (fun s => dualNorm 𝒩 (v θ s)) :=
      (dual_lip 𝒩).measurable.comp (hv_meas.comp (measurable_const.prodMk measurable_id))
    have hb : ∀ s, dualNorm 𝒩 (v θ s) ≤ M / 2 + dualNorm 𝒩 (v θ s) ^ 2 / (2 * M) := by
      intro s
      have e : M / 2 + dualNorm 𝒩 (v θ s) ^ 2 / (2 * M) - dualNorm 𝒩 (v θ s)
          = (dualNorm 𝒩 (v θ s) - M) ^ 2 / (2 * M) := by field_simp; ring
      have := div_nonneg (sq_nonneg (dualNorm 𝒩 (v θ s) - M)) (by positivity : (0:ℝ) ≤ 2 * M)
      linarith
    have hib : Integrable (fun s => M / 2 + dualNorm 𝒩 (v θ s) ^ 2 / (2 * M)) μ :=
      (integrable_const _).add (hi2.div_const _)
    have hi : Integrable (fun s => dualNorm 𝒩 (v θ s)) μ :=
      hib.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (dual_nonneg _ _)]; exact hb s)
    refine ⟨hi, ?_⟩
    calc ∫ s, dualNorm 𝒩 (v θ s) ∂μ ≤ ∫ s, (M / 2 + dualNorm 𝒩 (v θ s) ^ 2 / (2 * M)) ∂μ :=
          integral_mono hi hib hb
      _ = M / 2 + (∫ s, dualNorm 𝒩 (v θ s) ^ 2 ∂μ) / (2 * M) := by
          rw [integral_add (integrable_const _) (hi2.div_const _)]
          simp only [integral_const, probReal_univ, one_smul]
          rw [integral_div]
      _ ≤ M / 2 + M ^ 2 / (2 * M) := by gcongr
      _ = M := by field_simp; ring
  have hsgb : ∀ θ ∈ Θ, ∀ x, |⟪sgbar θ, x⟫| ≤ M * 𝒩.N x := by
    intro θ hθ x
    rw [← hv_mean θ hθ]
    have e : ⟪∫ s, v θ s ∂μ, x⟫ = ∫ s, ⟪v θ s, x⟫ ∂μ := by
      rw [real_inner_comm, ← integral_inner (hv_int θ hθ)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun s => real_inner_comm _ _)
    rw [e]
    have hint : Integrable (fun s => ⟪v θ s, x⟫) μ :=
      ((hv_int θ hθ).const_inner x).congr (Filter.Eventually.of_forall fun s => real_inner_comm _ _)
    calc |∫ s, ⟪v θ s, x⟫ ∂μ| ≤ ∫ s, |⟪v θ s, x⟫| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ s, dualNorm 𝒩 (v θ s) * 𝒩.N x ∂μ :=
          integral_mono hint.abs ((hdual1 θ hθ).1.mul_const _)
            (fun s => abs_inner_le_dual_mul 𝒩 _ _)
      _ = (∫ s, dualNorm 𝒩 (v θ s) ∂μ) * 𝒩.N x := integral_mul_const _ _
      _ ≤ M * 𝒩.N x := mul_le_mul_of_nonneg_right (hdual1 θ hθ).2 (N_nonneg _ _)
  have hlin1 : ∀ θ ∈ Θ, ∫⁻ s, ENNReal.ofReal (dualNorm 𝒩 (v θ s)) ∂μ ≤ ENNReal.ofReal M := by
    intro θ hθ
    rw [← ofReal_integral_eq_lintegral_ofReal (hdual1 θ hθ).1
      (Filter.Eventually.of_forall fun s => dual_nonneg _ _)]
    exact ENNReal.ofReal_le_ofReal (hdual1 θ hθ).2
  have hlin2 : ∀ θ ∈ Θ, ∫⁻ s, ENNReal.ofReal (dualNorm 𝒩 (v θ s) ^ 2) ∂μ
      ≤ ENNReal.ofReal (M ^ 2) := by
    intro θ hθ
    rw [← ofReal_integral_eq_lintegral_ofReal (hv_sq θ hθ).1
      (Filter.Eventually.of_forall fun s => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hv_sq θ hθ).2
  -- the per-step dual norms
  set q : Fin T → (Fin T → Ω) → ℝ := fun t ξ => dualNorm 𝒩 (v (θi t ξ) (ξ t)) with hq
  have hq0 : ∀ t ξ, 0 ≤ q t ξ := fun t ξ => dual_nonneg 𝒩 _
  have hvθm : ∀ t : Fin T, Measurable (fun ξ : Fin T → Ω => v (θi t ξ) (ξ t)) :=
    fun t => hv_meas.comp ((hθm t).prodMk (measurable_pi_apply t))
  have hqm : ∀ t, Measurable (q t) := fun t => (dual_lip 𝒩).measurable.comp (hvθm t)
  have hqinv : ∀ (s t : Fin T), s < t → ∀ ξ s', q s (Function.update ξ t s') = q s ξ := by
    intro s t hst ξ s'
    simp only [hq]
    rw [hinvθ t s (le_of_lt hst) ξ s', Function.update_of_ne (ne_of_lt hst)]
  have hLa : ∀ (t : Fin T) (X : (Fin T → Ω) → ENNReal), Measurable X →
      (∀ ξ s', X (Function.update ξ t s') = X ξ) →
      ∫⁻ ξ, ENNReal.ofReal (q t ξ) * X ξ ∂pm ≤ ENNReal.ofReal M * ∫⁻ ξ, X ξ ∂pm := by
    intro t X hX hXi
    have hH : Measurable (Function.uncurry
        (fun ξ s => ENNReal.ofReal (dualNorm 𝒩 (v (θi t ξ) s)) * X ξ)) :=
      (ENNReal.measurable_ofReal.comp ((dual_lip 𝒩).measurable.comp
        (hv_meas.comp (((hθm t).comp measurable_fst).prodMk measurable_snd)))).mul
        (hX.comp measurable_fst)
    have key := lintegral_resample μ t
      (fun ξ s => ENNReal.ofReal (dualNorm 𝒩 (v (θi t ξ) s)) * X ξ) hH
      (fun ξ s s' => by simp only [hinvθ t t le_rfl, hXi])
    calc ∫⁻ ξ, ENNReal.ofReal (q t ξ) * X ξ ∂pm
        = ∫⁻ ξ, ∫⁻ s, ENNReal.ofReal (dualNorm 𝒩 (v (θi t ξ) s)) * X ξ ∂μ ∂pm := key
      _ = ∫⁻ ξ, (∫⁻ s, ENNReal.ofReal (dualNorm 𝒩 (v (θi t ξ) s)) ∂μ) * X ξ ∂pm := by
          refine lintegral_congr (fun ξ => ?_)
          exact lintegral_mul_const _ (ENNReal.measurable_ofReal.comp ((dual_lip 𝒩).measurable.comp
            (hv_meas.comp (measurable_const.prodMk measurable_id))))
      _ ≤ ∫⁻ ξ, ENNReal.ofReal M * X ξ ∂pm :=
          lintegral_mono (fun ξ => mul_le_mul_left (hlin1 _ (hmem _ _)) _)
      _ = ENNReal.ofReal M * ∫⁻ ξ, X ξ ∂pm := lintegral_const_mul _ hX
  have hLb : ∀ t : Fin T, ∫⁻ ξ, ENNReal.ofReal (q t ξ ^ 2) ∂pm ≤ ENNReal.ofReal (M ^ 2) := by
    intro t
    have hH : Measurable (Function.uncurry
        (fun ξ s => ENNReal.ofReal (dualNorm 𝒩 (v (θi t ξ) s) ^ 2))) :=
      ENNReal.measurable_ofReal.comp (((dual_lip 𝒩).measurable.comp
        (hv_meas.comp (((hθm t).comp measurable_fst).prodMk measurable_snd))).pow_const 2)
    have key := lintegral_resample μ t
      (fun ξ s => ENNReal.ofReal (dualNorm 𝒩 (v (θi t ξ) s) ^ 2)) hH
      (fun ξ s s' => by simp only [hinvθ t t le_rfl])
    calc ∫⁻ ξ, ENNReal.ofReal (q t ξ ^ 2) ∂pm
        = ∫⁻ ξ, ∫⁻ s, ENNReal.ofReal (dualNorm 𝒩 (v (θi t ξ) s) ^ 2) ∂μ ∂pm := key
      _ ≤ ∫⁻ ξ, ENNReal.ofReal (M ^ 2) ∂pm := lintegral_mono (fun ξ => hlin2 _ (hmem _ _))
      _ = ENNReal.ofReal (M ^ 2) := by simp
  have hqI : ∀ t, Integrable (q t) pm := by
    intro t
    refine (lint_of_bound pm (q t) (hqm t) (hq0 t) (ENNReal.ofReal M) ENNReal.ofReal_lt_top ?_).1
    have := hLa t (fun _ => 1) measurable_const (fun _ _ => rfl)
    simpa using this
  have hq2I : ∀ t, Integrable (fun ξ => q t ξ ^ 2) pm ∧ ∫ ξ, q t ξ ^ 2 ∂pm ≤ M ^ 2 := by
    intro t
    have := lint_of_bound pm (fun ξ => q t ξ ^ 2) ((hqm t).pow_const 2) (fun ξ => sq_nonneg _)
      (ENNReal.ofReal (M ^ 2)) ENNReal.ofReal_lt_top (hLb t)
    refine ⟨this.1, this.2.trans ?_⟩
    rw [ENNReal.toReal_ofReal (sq_nonneg _)]
  have hqqlt : ∀ s t : Fin T, s < t → Integrable (fun ξ => q t ξ * q s ξ) pm := by
    intro s t hst
    have hXm : Measurable (fun ξ => ENNReal.ofReal (q s ξ)) := ENNReal.measurable_ofReal.comp (hqm s)
    have h1 := hLa t (fun ξ => ENNReal.ofReal (q s ξ)) hXm
      (fun ξ s' => by simp only [hqinv s t hst])
    have h2 : ∫⁻ ξ, ENNReal.ofReal (q s ξ) ∂pm ≤ ENNReal.ofReal M := by
      have := hLa s (fun _ => 1) measurable_const (fun _ _ => rfl)
      simpa using this
    refine (lint_of_bound pm _ ((hqm t).mul (hqm s)) (fun ξ => mul_nonneg (hq0 t ξ) (hq0 s ξ))
      (ENNReal.ofReal M * ENNReal.ofReal M) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ENNReal.ofReal_lt_top) ?_).1
    calc ∫⁻ ξ, ENNReal.ofReal (q t ξ * q s ξ) ∂pm
        = ∫⁻ ξ, ENNReal.ofReal (q t ξ) * ENNReal.ofReal (q s ξ) ∂pm := by
          refine lintegral_congr (fun ξ => ?_)
          rw [ENNReal.ofReal_mul (hq0 t ξ)]
      _ ≤ ENNReal.ofReal M * ∫⁻ ξ, ENNReal.ofReal (q s ξ) ∂pm := h1
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal M := by gcongr
  have hqqI : ∀ s t : Fin T, Integrable (fun ξ => q t ξ * q s ξ) pm := by
    intro s t
    rcases lt_trichotomy s t with hst | rfl | hts
    · exact hqqlt s t hst
    · exact (hq2I s).1.congr (Filter.Eventually.of_forall fun ξ => by ring)
    · exact (hqqlt t s hts).congr (Filter.Eventually.of_forall fun ξ => by ring)
  -- distance bound
  set N0 := 𝒩.N (θ0 - θbar) with hN0
  set S : (Fin T → Ω) → ℝ := fun ξ => ∑ s : Fin T, q s ξ with hS
  have hS0 : ∀ ξ, 0 ≤ S ξ := fun ξ => Finset.sum_nonneg (fun s _ => hq0 s ξ)
  have hdistP : ∀ t : ℕ, t ≤ T → ∀ ξ, 𝒩.N (θi t ξ - θbar)
      ≤ N0 + h / κ * ∑ s : Fin T, (if s.val < t then q s ξ else 0) := by
    intro t
    induction t with
    | zero => intro _ ξ; simp [hθi, bsmdIter, hN0]
    | succ t ih =>
      intro ht ξ
      have htT : t < T := by omega
      set tt : Fin T := ⟨t, htT⟩ with htt
      have hs := hstep tt ξ
      have hsl := step_le Θ hΘv 𝒩 κ ω ω' hω prox hprox (θi t ξ) (hmem t ξ) h hh.le
        (v (θi t ξ) (ξ tt))
      have htri := 𝒩.add_le (θi (t + 1) ξ - θi t ξ) (θi t ξ - θbar)
      rw [show θi (t + 1) ξ - θi t ξ + (θi t ξ - θbar) = θi (t + 1) ξ - θbar by abel] at htri
      have hsplit : ∑ s : Fin T, (if s.val < t + 1 then q s ξ else 0)
          = ∑ s : Fin T, (if s.val < t then q s ξ else 0) + q tt ξ := by
        have : ∀ s : Fin T, (if s.val < t + 1 then q s ξ else 0)
            = (if s.val < t then q s ξ else 0) + (if s = tt then q s ξ else 0) := by
          intro s
          by_cases h1 : s.val < t
          · have : s ≠ tt := by intro he; rw [he] at h1; simp [htt] at h1
            simp [h1, this, show s.val < t + 1 by omega]
          · by_cases h2 : s = tt
            · subst h2; simp [htt]
            · have : ¬ s.val < t + 1 := by
                intro h3; apply h2; ext; simp [htt]; omega
              simp [h1, h2, this]
        rw [Finset.sum_congr rfl (fun s _ => this s), Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp
      rw [hsplit]
      have hstepN : 𝒩.N (θi (t + 1) ξ - θi t ξ) ≤ h / κ * q tt ξ := by
        rw [hs, div_mul_eq_mul_div, le_div_iff₀ hκ, mul_comm]; exact hsl
      have := ih (by omega) ξ
      nlinarith
  have hdist : ∀ t : Fin T, ∀ ξ, 𝒩.N (θi t ξ - θbar) ≤ N0 + h / κ * S ξ := by
    intro t ξ
    refine (hdistP t t.isLt.le ξ).trans ?_
    gcongr
    refine Finset.sum_le_sum (fun s _ => ?_)
    split_ifs
    · exact le_rfl
    · exact hq0 s ξ
  have hSI : Integrable S pm := integrable_finsetSum _ (fun s _ => hqI s)
  -- the noisy inner products
  set W : Fin T → (Fin T → Ω) → ℝ := fun t ξ => ⟪v (θi t ξ) (ξ t), θi t ξ - θbar⟫ with hW
  have hWm : ∀ t, Measurable (W t) := fun t => (hvθm t).inner ((hθm t).sub measurable_const)
  have hWI : ∀ t, Integrable (W t) pm := by
    intro t
    have hb : Integrable (fun ξ => N0 * q t ξ + h / κ * ∑ s : Fin T, q t ξ * q s ξ) pm :=
      ((hqI t).const_mul _).add ((integrable_finsetSum _ (fun s _ => hqqI s t)).const_mul _)
    refine hb.mono' (hWm t).aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs]
    calc |W t ξ| ≤ q t ξ * 𝒩.N (θi t ξ - θbar) := abs_inner_le_dual_mul 𝒩 _ _
      _ ≤ q t ξ * (N0 + h / κ * S ξ) := mul_le_mul_of_nonneg_left (hdist t ξ) (hq0 t ξ)
      _ = N0 * q t ξ + h / κ * ∑ s : Fin T, q t ξ * q s ξ := by
          simp only [hS]; rw [← Finset.mul_sum]; ring
  -- the mean inner products
  set mfun : Param d → Param d := fun θ => ∫ s, v θ s ∂μ with hmfun
  have hmfm : Measurable mfun :=
    (hv_meas.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have hmf_eq : ∀ t ξ, mfun (θi t ξ) = sgbar (θi t ξ) := fun t ξ => hv_mean _ (hmem t ξ)
  set Wm : Fin T → (Fin T → Ω) → ℝ := fun t ξ => ⟪mfun (θi t ξ), θi t ξ - θbar⟫ with hWmdef
  have hWmm : ∀ t, Measurable (Wm t) :=
    fun t => (hmfm.comp (hθm t)).inner ((hθm t).sub measurable_const)
  have hWmb : ∀ t ξ, |Wm t ξ| ≤ M * (N0 + h / κ * S ξ) := by
    intro t ξ
    simp only [hWmdef]
    rw [hmf_eq]
    exact (hsgb _ (hmem t ξ) _).trans (mul_le_mul_of_nonneg_left (hdist t ξ) hM.le)
  have hWmI : ∀ t, Integrable (Wm t) pm := by
    intro t
    refine (((integrable_const N0).add (hSI.const_mul (h / κ))).const_mul M).mono'
      (hWmm t).aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs]; exact hWmb t ξ
  have hWeq : ∀ t, ∫ ξ, W t ξ ∂pm = ∫ ξ, Wm t ξ ∂pm := by
    intro t
    have hH : Measurable (Function.uncurry (fun ξ s => ⟪v (θi t ξ) s, θi t ξ - θbar⟫)) :=
      (hv_meas.comp (((hθm t).comp measurable_fst).prodMk measurable_snd)).inner
        (((hθm t).comp measurable_fst).sub measurable_const)
    have key := integral_resample μ t (fun ξ s => ⟪v (θi t ξ) s, θi t ξ - θbar⟫) hH
      (fun ξ s s' => by simp only [hinvθ t t le_rfl]) (hWI t)
    refine key.trans (integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_))
    show ∫ s, ⟪v (θi t ξ) s, θi t ξ - θbar⟫ ∂μ = ⟪∫ s, v (θi t ξ) s ∂μ, θi t ξ - θbar⟫
    rw [real_inner_comm (θi t ξ - θbar) _, ← integral_inner (hv_int _ (hmem t ξ))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s => real_inner_comm _ _)
  -- pathwise mirror-descent inequality
  have hpath : ∀ ξ, h * ∑ t : Fin T, W t ξ ≤ D + h ^ 2 / (2 * κ) * ∑ t : Fin T, q t ξ ^ 2 := by
    intro ξ
    set e : ℕ → ℝ := fun t => bregman ω ω' (θi t ξ) θbar with he
    have hone : ∀ t : Fin T, h * W t ξ - h ^ 2 / (2 * κ) * q t ξ ^ 2 ≤ e t - e (t + 1) := by
      intro t
      have := one_step Θ hΘv 𝒩 κ ω ω' hω prox hprox (θi t ξ) (hmem t ξ) θbar hθbar.1 h hh.le
        (v (θi t ξ) (ξ t))
      simp only [he, hW, hq]
      rw [hstep t ξ]
      have e2 : h ^ 2 / (2 * κ) * dualNorm 𝒩 (v (θi (↑t) ξ) (ξ t)) ^ 2
          = h ^ 2 * dualNorm 𝒩 (v (θi (↑t) ξ) (ξ t)) ^ 2 / (2 * κ) := by ring
      rw [e2]; linarith
    have htel : ∑ t : Fin T, (e t - e (t + 1)) = e 0 - e T := by
      rw [Fin.sum_univ_eq_sum_range (fun t => e t - e (t + 1)) T, Finset.sum_range_sub']
    have heT : 0 ≤ e T := le_trans (by positivity)
      (bregman_lower Θ hΘv 𝒩 κ ω ω' hω _ θbar (hmem T ξ) hθbar.1)
    have he0 : e 0 = D := rfl
    have := Finset.sum_le_sum (fun (t : Fin T) (_ : t ∈ Finset.univ) => hone t)
    rw [htel, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
    linarith
  -- pathwise convexity bound
  have hFpath : ∀ ξ : Fin T → Ω, F (bsmdAvg prox v h θ0 ξ) ≤ ΔF + Fbar θbar + (T:ℝ)⁻¹ * ∑ t : Fin T, Wm t ξ := by
    intro ξ
    set θh := bsmdAvg prox v h θ0 ξ with hθh
    have hsum1 : ∑ _t : Fin T, (T:ℝ)⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
    have hθhm : θh ∈ Θ := by
      rw [hθh, havg, Finset.smul_sum]
      exact hΘv.sum_mem (fun _ _ => inv_nonneg.mpr hTpos.le) hsum1 (fun t _ => hmem t ξ)
    have hsumθ : ∑ t : Fin T, θi t ξ = (T:ℝ) • θh := by
      rw [hθh, havg, smul_smul, mul_inv_cancel₀ hTpos.ne', one_smul]
    have h1 := hbias θh hθhm
    have hJ : Fbar θh ≤ (T:ℝ)⁻¹ * ∑ t : Fin T, Fbar (θi t ξ) := by
      have hsum : ∑ t : Fin T, ⟪sgbar θh, θi t ξ - θh⟫ = 0 := by
        rw [← inner_sum, Finset.sum_sub_distrib, hsumθ, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, sub_self, inner_zero_right]
      have := Finset.sum_le_sum (fun (t : Fin T) (_ : t ∈ Finset.univ) =>
        hsgbar θh hθhm (θi t ξ) (hmem t ξ))
      rw [Finset.sum_add_distrib, hsum, add_zero, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] at this
      rw [le_inv_mul_iff₀ hTpos]; linarith
    have hK : ∀ t : Fin T, Fbar (θi t ξ) ≤ Fbar θbar + Wm t ξ := by
      intro t
      have := hsgbar _ (hmem t ξ) θbar hθbar.1
      simp only [hWmdef]
      rw [hmf_eq]
      have e : ⟪sgbar (θi t ξ), θbar - θi t ξ⟫ = -⟪sgbar (θi t ξ), θi t ξ - θbar⟫ := by
        rw [← inner_neg_right, neg_sub]
      linarith
    have hK2 : (T:ℝ)⁻¹ * ∑ t : Fin T, Fbar (θi t ξ) ≤ Fbar θbar + (T:ℝ)⁻¹ * ∑ t : Fin T, Wm t ξ := by
      have := Finset.sum_le_sum (fun (t : Fin T) (_ : t ∈ Finset.univ) => hK t)
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at this
      have h2 := mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hTpos.le)
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hTpos.ne', one_mul] at h2
      exact h2
    have := abs_le.mp h1
    linarith
  have hFlow : ∀ ξ : Fin T → Ω, Fbar θbar - ΔF ≤ F (bsmdAvg prox v h θ0 ξ) := by
    intro ξ
    have hθhm : bsmdAvg prox v h θ0 ξ ∈ Θ := by
      have hsum1 : ∑ _t : Fin T, (T:ℝ)⁻¹ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
      rw [havg, Finset.smul_sum]
      exact hΘv.sum_mem (fun _ _ => inv_nonneg.mpr hTpos.le) hsum1 (fun t _ => hmem t ξ)
    have h1 := abs_le.mp (hbias _ hθhm)
    have h2 := hθbar.2 _ hθhm
    linarith
  -- integrability of F(θ̂)
  have hθhmeas : Measurable (fun ξ : Fin T → Ω => bsmdAvg prox v h θ0 ξ) := by
    have : (fun ξ : Fin T → Ω => bsmdAvg prox v h θ0 ξ)
        = fun ξ => (T:ℝ)⁻¹ • ∑ t : Fin T, θi t ξ := funext havg
    rw [this]
    exact (Finset.measurable_sum (Finset.univ : Finset (Fin T)) (fun t _ => hθm t)).const_smul ((T:ℝ)⁻¹)
  have hFI : Integrable (fun ξ : Fin T → Ω => F (bsmdAvg prox v h θ0 ξ)) pm := by
    have hb : Integrable (fun ξ => |Fbar θbar| + |ΔF| + M * (N0 + h / κ * S ξ)) pm :=
      (integrable_const _).add (((integrable_const N0).add (hSI.const_mul (h / κ))).const_mul M)
    refine hb.mono' (hF_meas.comp hθhmeas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have hup := hFpath ξ
    have hlo := hFlow ξ
    have hsumW : (T:ℝ)⁻¹ * ∑ t : Fin T, Wm t ξ ≤ M * (N0 + h / κ * S ξ) := by
      have := Finset.sum_le_sum (fun (t : Fin T) (_ : t ∈ Finset.univ) => (abs_le.mp (hWmb t ξ)).2)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      rw [inv_mul_le_iff₀ hTpos]; linarith
    have hMN : 0 ≤ M * (N0 + h / κ * S ξ) := by
      have := N_nonneg 𝒩 (θ0 - θbar)
      have := hS0 ξ
      positivity
    constructor
    · linarith [neg_abs_le (Fbar θbar), le_abs_self ΔF, neg_abs_le ΔF]
    · linarith [le_abs_self (Fbar θbar), le_abs_self ΔF]
  refine ⟨hFI, ?_⟩
  -- integrate
  have hint_path : h * ∑ t : Fin T, ∫ ξ, W t ξ ∂pm ≤ D + h ^ 2 / (2 * κ) * (T * M ^ 2) := by
    have hL : Integrable (fun ξ => h * ∑ t : Fin T, W t ξ) pm :=
      (integrable_finsetSum _ (fun t _ => hWI t)).const_mul h
    have hR : Integrable (fun ξ => D + h ^ 2 / (2 * κ) * ∑ t : Fin T, q t ξ ^ 2) pm :=
      (integrable_const D).add
        ((integrable_finsetSum _ (fun t _ => (hq2I t).1)).const_mul _)
    have := integral_mono hL hR hpath
    rw [integral_const_mul, integral_finsetSum _ (fun t _ => hWI t),
      integral_add (integrable_const D) ((integrable_finsetSum _ (fun t _ => (hq2I t).1)).const_mul _),
      integral_const_mul, integral_finsetSum _ (fun t _ => (hq2I t).1)] at this
    simp only [integral_const, probReal_univ, one_smul] at this
    have hsq : ∑ t : Fin T, ∫ ξ, q t ξ ^ 2 ∂pm ≤ T * M ^ 2 := by
      have := Finset.sum_le_sum (fun (t : Fin T) (_ : t ∈ Finset.univ) => (hq2I t).2)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      exact this
    have hc : 0 ≤ h ^ 2 / (2 * κ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsq hc]
  have hint_F : ∫ ξ, F (bsmdAvg prox v h θ0 ξ) ∂pm
      ≤ ΔF + Fbar θbar + (T:ℝ)⁻¹ * ∑ t : Fin T, ∫ ξ, W t ξ ∂pm := by
    have hR : Integrable (fun ξ => ΔF + Fbar θbar + (T:ℝ)⁻¹ * ∑ t : Fin T, Wm t ξ) pm :=
      (integrable_const _).add ((integrable_finsetSum _ (fun t _ => hWmI t)).const_mul _)
    have := integral_mono hFI hR hFpath
    rw [integral_add (integrable_const _) ((integrable_finsetSum _ (fun t _ => hWmI t)).const_mul _),
      integral_const_mul, integral_finsetSum _ (fun t _ => hWmI t)] at this
    simp only [integral_const, probReal_univ, one_smul] at this
    rw [Finset.sum_congr rfl (fun t _ => hWeq t)]
    exact this
  have hstar : Fbar θbar - ΔF ≤ F θstar := by
    have h1 := abs_le.mp (hbias θstar hθstar.1)
    have h2 := hθbar.2 θstar hθstar.1
    linarith
  rw [integral_sub hFI (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul]
  have hfin : (T:ℝ)⁻¹ * ∑ t : Fin T, ∫ ξ, W t ξ ∂pm ≤ D / (h * T) + h * M ^ 2 / (2 * κ) := by
    rw [inv_mul_le_iff₀ hTpos]
    have := hint_path
    rw [← le_div_iff₀' hh] at this
    calc ∑ t : Fin T, ∫ ξ, W t ξ ∂pm ≤ (D + h ^ 2 / (2 * κ) * (T * M ^ 2)) / h := this
      _ = T * (D / (h * T) + h * M ^ 2 / (2 * κ)) := by field_simp
  linarith

end Aux_BSMD7

open SinkhornDRO.BSMD Aux_BSMD7 in
theorem solution {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (Θ : Set (Param d)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ)
    (𝒩 : MirrorNorm d) (κ : ℝ) (ω : Param d → ℝ) (ω' : Param d → Param d)
    (hω : IsDistGen Θ 𝒩 κ ω ω')
    (prox : Param d → Param d → Param d) (hprox : IsProxMap Θ ω ω' prox)
    (hprox_meas : Measurable (Function.uncurry prox))
    (F Fbar : Param d → ℝ) (hF_meas : Measurable F) (ΔF : ℝ)
    (hbias : ∀ θ ∈ Θ, |Fbar θ - F θ| ≤ ΔF)
    (sgbar : Param d → Param d)
    (hsgbar : ∀ θ ∈ Θ, ∀ θ' ∈ Θ, Fbar θ + ⟪sgbar θ, θ' - θ⟫ ≤ Fbar θ')
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (v : Param d → Ω → Param d) (hv_meas : Measurable (Function.uncurry v))
    (M : ℝ) (hM : 0 < M)
    (hv_int : ∀ θ ∈ Θ, Integrable (v θ) μ)
    (hv_mean : ∀ θ ∈ Θ, ∫ s, v θ s ∂μ = sgbar θ)
    (hv_sq : ∀ θ ∈ Θ, Integrable (fun s => dualNorm 𝒩 (v θ s) ^ 2) μ ∧
      ∫ s, dualNorm 𝒩 (v θ s) ^ 2 ∂μ ≤ M ^ 2)
    (θbar : Param d) (hθbar : θbar ∈ Θ ∧ ∀ θ ∈ Θ, Fbar θbar ≤ Fbar θ)
    (θstar : Param d) (hθstar : θstar ∈ Θ ∧ ∀ θ ∈ Θ, F θstar ≤ F θ)
    (θ0 : Param d) (hθ0 : θ0 ∈ Θ)
    (T : ℕ) (hT : 0 < T) :
    let h := Real.sqrt (2 * κ * bregman ω ω' θ0 θbar / (T * M ^ 2))
    Integrable (fun ξ : Fin T → Ω => F (bsmdAvg prox v h θ0 ξ)) (Measure.pi fun _ => μ) ∧
      ∫ ξ, (F (bsmdAvg prox v h θ0 ξ) - F θstar) ∂(Measure.pi fun _ : Fin T => μ)
        ≤ 2 * ΔF + M * Real.sqrt (2 * bregman ω ω' θ0 θbar / (κ * T)) := by
  intro h
  classical
  have hκ : 0 < κ := hω.2.2.1
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT
  set D := bregman ω ω' θ0 θbar with hD
  have hD0 : 0 ≤ D := le_trans (by positivity)
    (bregman_lower Θ hΘv 𝒩 κ ω ω' hω θ0 θbar hθ0 hθbar.1)
  rcases eq_or_lt_of_le hD0 with hDz | hDpos
  · -- degenerate case `D = 0`: the step is zero and `θ0 = θbar`
    have hh : h = 0 := by
      show Real.sqrt (2 * κ * D / (T * M ^ 2)) = 0
      rw [← hDz]; simp
    have hθb : θ0 = θbar := by
      have := bregman_lower Θ hΘv 𝒩 κ ω ω' hω θ0 θbar hθ0 hθbar.1
      rw [← hD, ← hDz] at this
      have hN : 𝒩.N (θbar - θ0) = 0 := by
        have h1 := N_nonneg 𝒩 (θbar - θ0)
        have : 𝒩.N (θbar - θ0) ^ 2 ≤ 0 := by nlinarith
        nlinarith
      exact (sub_eq_zero.mp (N_eq_zero 𝒩 _ hN)).symm
    have hconst : ∀ (ξ : Fin T → Ω) (t : ℕ), bsmdIter prox v h θ0 ξ t = θ0 := by
      intro ξ t
      induction t with
      | zero => rfl
      | succ t ih =>
        by_cases ht : t < T
        · simp only [bsmdIter, dif_pos ht]
          rw [ih]
          have hsl := step_le Θ hΘv 𝒩 κ ω ω' hω prox hprox θ0 hθ0 h (by rw [hh])
            (v θ0 (ξ ⟨t, ht⟩))
          rw [hh, zero_mul] at hsl
          have hN : 𝒩.N (prox θ0 (h • v θ0 (ξ ⟨t, ht⟩)) - θ0) = 0 := by
            have := N_nonneg 𝒩 (prox θ0 (h • v θ0 (ξ ⟨t, ht⟩)) - θ0)
            rw [← hh] at hsl
            nlinarith
          exact sub_eq_zero.mp (N_eq_zero 𝒩 _ hN)
        · simp only [bsmdIter, dif_neg ht]; exact ih
    have havg : ∀ ξ : Fin T → Ω, bsmdAvg prox v h θ0 ξ = θbar := by
      intro ξ
      unfold bsmdAvg
      simp only [hconst ξ, Finset.sum_const, Finset.card_range]
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hTpos.ne', one_smul, hθb]
    simp only [havg]
    refine ⟨integrable_const _, ?_⟩
    simp only [integral_const, probReal_univ, one_smul]
    have h1 := abs_le.mp (hbias θbar hθbar.1)
    have h2 := abs_le.mp (hbias θstar hθstar.1)
    have h3 := hθbar.2 θstar hθstar.1
    have h4 : M * Real.sqrt (2 * D / (κ * T)) = 0 := by rw [← hDz]; simp
    rw [h4]
    linarith
  · -- main case
    have hhpos : 0 < h := Real.sqrt_pos.mpr (by positivity)
    obtain ⟨hI, hB⟩ := main_bound Θ hΘv 𝒩 κ ω ω' hω prox hprox hprox_meas F Fbar hF_meas ΔF hbias
      sgbar hsgbar μ v hv_meas M hM hv_int hv_mean hv_sq θbar hθbar θstar hθstar θ0 hθ0 T hT h hhpos
    refine ⟨hI, hB.trans (le_of_eq ?_)⟩
    -- `D/(hT) + h M²/(2κ) = M √(2D/(κT))`
    set r := Real.sqrt (2 * D / (κ * T)) with hr
    have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
    have hr2 : r ^ 2 = 2 * D / (κ * T) := Real.sq_sqrt (by positivity)
    have hhr : h = κ * r / M := by
      have e : 2 * κ * D / (T * M ^ 2) = (κ * r / M) ^ 2 := by
        rw [div_pow, mul_pow, hr2]; field_simp
      show Real.sqrt (2 * κ * D / (T * M ^ 2)) = _
      rw [e, Real.sqrt_sq (by positivity)]
    rw [← hD, hhr]
    have hDr : D = r ^ 2 * κ * T / 2 := by rw [hr2]; field_simp
    rw [hDr]
    field_simp
    ring
