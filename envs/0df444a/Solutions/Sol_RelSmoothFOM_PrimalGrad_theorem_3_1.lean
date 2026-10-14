-- Prove2me | solution 1 for RelSmoothFOM.PrimalGrad.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:37:26.694987+00:00
-- url     : https://prove2.me/submissions/34032d8e-808a-4eca-b75a-19d3ee69d070

import Mathlib
import Definitions.Def_RelSmoothFOM_PrimalGrad_Setting

open Filter Topology

set_option linter.unusedSectionVars false

namespace RRAux_RSF

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma mem_ri_iff {Q : Set E} {z : E} :
    z ∈ intrinsicInterior ℝ Q ↔ z ∈ affineSpan ℝ Q ∧
      ∃ u ∈ 𝓝 z, ∀ w ∈ affineSpan ℝ Q, w ∈ u → w ∈ Q := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    rw [mem_interior_iff_mem_nhds, mem_nhds_subtype] at hy
    obtain ⟨u, hu, hsub⟩ := hy
    exact ⟨u, hu, fun w hw hwu => hsub (show (⟨w, hw⟩ : affineSpan ℝ Q) ∈ Subtype.val ⁻¹' u from hwu)⟩
  · rintro ⟨hz, u, hu, hsub⟩
    refine ⟨⟨z, hz⟩, ?_, rfl⟩
    rw [mem_interior_iff_mem_nhds, mem_nhds_subtype]
    exact ⟨u, hu, fun w hw => hsub w.1 w.2 hw⟩

lemma memA {Q : Set E} {a b : E} (s : ℝ) (ha : a ∈ affineSpan ℝ Q) (hb : b ∈ affineSpan ℝ Q) :
    a + s • (b - a) ∈ affineSpan ℝ Q := by
  have := AffineMap.lineMap_mem s ha hb
  rw [AffineMap.lineMap_apply_module'] at this
  rwa [add_comm]

lemma ri_segment {Q : Set E} (hQ : Convex ℝ Q) {x z : E} (hx : x ∈ Q)
    (hz : z ∈ intrinsicInterior ℝ Q) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    x + t • (z - x) ∈ intrinsicInterior ℝ Q := by
  rw [mem_ri_iff] at hz ⊢
  obtain ⟨hzA, u, hu, hsub⟩ := hz
  have hxA : x ∈ affineSpan ℝ Q := subset_affineSpan ℝ Q hx
  refine ⟨memA t hxA hzA, (fun y => x + t⁻¹ • (y - x)) ⁻¹' u, ?_, ?_⟩
  · apply ContinuousAt.preimage_mem_nhds (by fun_prop)
    convert hu using 1
    simp [smul_smul, inv_mul_cancel₀ ht0.ne']
  · intro w hw hwu
    have hg : x + t⁻¹ • (w - x) ∈ Q := hsub _ (memA t⁻¹ hxA hw) hwu
    have := hQ.add_smul_sub_mem hx hg ⟨ht0.le, ht1⟩
    convert this using 1
    simp [smul_smul, mul_inv_cancel₀ ht0.ne']

lemma ri_convex {Q : Set E} (hQ : Convex ℝ Q) : Convex ℝ (intrinsicInterior ℝ Q) := by
  intro a ha b hb s t hs ht hst
  rcases ht.eq_or_lt with rfl | htpos
  · have : s = 1 := by linarith
    subst this; simpa using ha
  · have := ri_segment hQ (intrinsicInterior_subset ha) hb htpos (by linarith)
    convert this using 1
    rw [show s = 1 - t by linarith]; module

lemma convexOn_of_grad {S : Set E} (hS : Convex ℝ S) (g : E → ℝ) (G : E → E →L[ℝ] ℝ)
    (hg : ∀ a ∈ S, ∀ b ∈ S, g a + G a (b - a) ≤ g b) : ConvexOn ℝ S g := by
  refine ⟨hS, fun a ha b hb s t hs ht hst => ?_⟩
  have hc : s • a + t • b ∈ S := hS ha hb hs ht hst
  have h1 := hg _ hc a ha
  have h2 := hg _ hc b hb
  have h0 : s * G (s • a + t • b) (a - (s • a + t • b)) + t * G (s • a + t • b) (b - (s • a + t • b)) = 0 := by
    rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← map_add]
    convert map_zero (G (s • a + t • b)) using 2
    rw [show s = 1 - t by linarith]; module
  have h1' := mul_le_mul_of_nonneg_left h1 hs
  have h2' := mul_le_mul_of_nonneg_left h2 ht
  simp only [smul_eq_mul]
  have : g (s • a + t • b) = (s + t) * g (s • a + t • b) := by rw [hst, one_mul]
  nlinarith

lemma convexOn_ext {Q : Set E} (hQ : Convex ℝ Q) (g : E → ℝ) (hgc : ∀ a ∈ Q, ContinuousAt g a)
    (hri : ConvexOn ℝ (intrinsicInterior ℝ Q) g) : ConvexOn ℝ Q g := by
  refine ⟨hQ, fun a ha b hb s t hs ht hst => ?_⟩
  obtain ⟨z, hz⟩ := Set.Nonempty.intrinsicInterior hQ ⟨a, ha⟩
  have key : ∀ τ ∈ Set.Ioc (0:ℝ) 1, g ((s • a + t • b) + τ • (z - (s • a + t • b))) ≤
      s * g (a + τ • (z - a)) + t * g (b + τ • (z - b)) := by
    intro τ hτ
    have := hri.2 (ri_segment hQ ha hz hτ.1 hτ.2) (ri_segment hQ hb hz hτ.1 hτ.2) hs ht hst
    have e : s • (a + τ • (z - a)) + t • (b + τ • (z - b)) =
        (s • a + t • b) + τ • (z - (s • a + t • b)) := by
      rw [show s = 1 - t by linarith]; module
    rw [e] at this; simpa [smul_eq_mul] using this
  have lim : ∀ c ∈ Q, Tendsto (fun τ : ℝ => g (c + τ • (z - c))) (𝓝[>] 0) (𝓝 (g c)) := by
    intro c hc
    have h1 : Tendsto (fun τ : ℝ => c + τ • (z - c)) (𝓝 0) (𝓝 c) := by
      have : Continuous (fun τ : ℝ => c + τ • (z - c)) := by fun_prop
      simpa using this.tendsto 0
    exact ((hgc c hc).tendsto.comp h1).mono_left nhdsWithin_le_nhds
  have hp : s • a + t • b ∈ Q := hQ ha hb hs ht hst
  simp only [smul_eq_mul]
  refine le_of_tendsto_of_tendsto (lim _ hp) (((lim a ha).const_mul s).add ((lim b hb).const_mul t)) ?_
  filter_upwards [Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with τ hτ
  exact key τ hτ

lemma grad_of_convexOn {Q : Set E} (g : E → ℝ) (hg : ConvexOn ℝ Q g) {a b : E} (ha : a ∈ Q)
    (hb : b ∈ Q) (hd : DifferentiableAt ℝ g a) :
    g a + fderiv ℝ g a (b - a) ≤ g b := by
  have h1 : HasDerivAt (fun τ : ℝ => a + τ • (b - a)) (b - a) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (b - a)).const_add a
  have h2 : HasFDerivAt g (fderiv ℝ g a) (a + (0:ℝ) • (b - a)) := by
    simpa using hd.hasFDerivAt
  have hderiv := h2.comp_hasDerivAt (0:ℝ) h1
  have tend := hderiv.tendsto_slope_zero_right
  have hle : fderiv ℝ g a (b - a) ≤ g b - g a := by
    refine le_of_tendsto tend ?_
    filter_upwards [Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with τ hτ
    have := hg.2 ha hb (by linarith [hτ.2] : 0 ≤ 1 - τ) hτ.1.le (by ring)
    have e : (1 - τ) • a + τ • b = a + τ • (b - a) := by module
    rw [e] at this
    simp only [Function.comp, zero_add, zero_smul, add_zero, smul_eq_mul] at this ⊢
    rw [inv_mul_le_iff₀ hτ.1]
    nlinarith
  linarith

lemma ext_grad {Q : Set E} (hQ : Convex ℝ Q) (g : E → ℝ) (hgd : ∀ a ∈ Q, DifferentiableAt ℝ g a)
    (hri : ∀ a ∈ intrinsicInterior ℝ Q, ∀ b ∈ intrinsicInterior ℝ Q,
      g a + fderiv ℝ g a (b - a) ≤ g b) :
    ∀ a ∈ Q, ∀ b ∈ Q, g a + fderiv ℝ g a (b - a) ≤ g b := by
  have c1 := convexOn_of_grad (ri_convex hQ) g (fderiv ℝ g) hri
  have c2 := convexOn_ext hQ g (fun a ha => (hgd a ha).continuousAt) c1
  exact fun a ha b hb => grad_of_convexOn g c2 ha hb (hgd a ha)

end RRAux_RSF
namespace RRAux_NUM

lemma rate1 (L μ : ℝ) (hμ : 0 ≤ μ) (hμL : μ < L) (e D : ℕ → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hK : ∀ i, e (i+1) ≤ L * D i - μ * D i - L * D (i+1)) (hmono : ∀ i, e (i+1) ≤ e i) :
    ∀ k : ℕ, 1 ≤ k → e k ≤ (L - μ) / (k : ℝ) * D 0 := by
  have main : ∀ k : ℕ, (k:ℝ) * e k ≤ (L - μ) * (D 0 - D k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      push_cast
      have h1 := mul_le_mul_of_nonneg_left (hmono k) (Nat.cast_nonneg (α := ℝ) k)
      have h2 := hK k
      have h3 := mul_nonneg hμ (hD (k+1))
      nlinarith
  intro k hk
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  have := main k
  have h4 := mul_nonneg (sub_nonneg.mpr hμL.le) (hD k)
  rw [div_mul_eq_mul_div, le_div_iff₀ hkpos]
  nlinarith

lemma rate2 (L μ : ℝ) (hμ : 0 < μ) (hμL : μ < L) (e D : ℕ → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hK : ∀ i, e (i+1) ≤ L * D i - μ * D i - L * D (i+1)) (hmono : ∀ i, e (i+1) ≤ e i) :
    ∀ k : ℕ, 1 ≤ k →
      e k ≤ μ * D 0 / ((1 + μ / (L - μ)) ^ k - 1) ∧
      μ * D 0 / ((1 + μ / (L - μ)) ^ k - 1) ≤ (L - μ) / (k : ℝ) * D 0 := by
  have hLμ : 0 < L - μ := sub_pos.mpr hμL
  set r := μ / (L - μ) with hrdef
  have hr0 : 0 < r := div_pos hμ hLμ
  have hr : r * (L - μ) = μ := by rw [hrdef]; field_simp
  have main : ∀ k : ℕ, ((1 + r) ^ k - 1) * e k ≤ μ * (D 0 - (1 + r) ^ k * D k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hqk : 1 ≤ (1 + r) ^ k := one_le_pow₀ (by linarith)
      have h1 := mul_le_mul_of_nonneg_left (hmono k) (sub_nonneg.mpr hqk)
      have h2 := mul_le_mul_of_nonneg_left (hK k) (mul_nonneg (by positivity : (0:ℝ) ≤ (1 + r) ^ k) hr0.le)
      rw [pow_succ]
      linear_combination h1 + h2 + ih + ((1 + r) ^ k * D k - (1 + r) ^ k * D (k+1)) * hr
  intro k hk
  have hpow : 1 + (k:ℝ) * r ≤ (1 + r) ^ k := one_add_mul_le_pow (by linarith) k
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  have hkr : 0 < (k:ℝ) * r := mul_pos hkpos hr0
  have hden : 0 < (1 + r) ^ k - 1 := by linarith
  constructor
  · rw [le_div_iff₀ hden]
    have := main k
    have h4 := mul_nonneg hμ.le (mul_nonneg (by positivity : (0:ℝ) ≤ (1 + r) ^ k) (hD k))
    nlinarith
  · calc μ * D 0 / ((1 + r) ^ k - 1) ≤ μ * D 0 / ((k:ℝ) * r) :=
          div_le_div_of_nonneg_left (mul_nonneg hμ.le (hD 0)) hkr (by linarith)
      _ = (L - μ) / (k : ℝ) * D 0 := by
          rw [hrdef]; field_simp

end RRAux_NUM

namespace RRAux_PG

open RelSmoothFOM.PrimalGrad

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma smooth_ext (Q : Set E) (hQ : Convex ℝ Q) (f h : E → ℝ)
    (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (L : ℝ)
    (hsm : IsRelSmooth Q f h L) :
    ∀ a ∈ Q, ∀ b ∈ Q, f b ≤ f a + fderiv ℝ f a (b - a) + L * bregman h b a := by
  have hgd : ∀ a ∈ Q, HasFDerivAt (fun y => L * h y - f y)
      (L • fderiv ℝ h a - fderiv ℝ f a) a :=
    fun a ha => ((hhd a ha).hasFDerivAt.const_mul L).sub (hfd a ha).hasFDerivAt
  have key := RRAux_RSF.ext_grad hQ (fun y => L * h y - f y)
    (fun a ha => (hgd a ha).differentiableAt) (by
      intro a ha b hb
      rw [(hgd a (intrinsicInterior_subset ha)).fderiv]
      have := hsm a ha b hb
      simp only [bregman] at this
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      linarith)
  intro a ha b hb
  have := key a ha b hb
  rw [(hgd a ha).fderiv] at this
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at this
  simp only [bregman]
  linarith

lemma sc_ext (Q : Set E) (hQ : Convex ℝ Q) (f h : E → ℝ)
    (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (μ : ℝ)
    (hsc : IsRelStronglyConvex Q f h μ) :
    ∀ a ∈ Q, ∀ b ∈ Q, f a + fderiv ℝ f a (b - a) + μ * bregman h b a ≤ f b := by
  have hgd : ∀ a ∈ Q, HasFDerivAt (fun y => f y - μ * h y)
      (fderiv ℝ f a - μ • fderiv ℝ h a) a :=
    fun a ha => (hfd a ha).hasFDerivAt.sub ((hhd a ha).hasFDerivAt.const_mul μ)
  have key := RRAux_RSF.ext_grad hQ (fun y => f y - μ * h y)
    (fun a ha => (hgd a ha).differentiableAt) (by
      intro a ha b hb
      rw [(hgd a (intrinsicInterior_subset ha)).fderiv]
      have := hsc a ha b hb
      simp only [bregman] at this
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      linarith)
  intro a ha b hb
  have := key a ha b hb
  rw [(hgd a ha).fderiv] at this
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at this
  simp only [bregman]
  linarith

lemma bregman_nonneg (Q : Set E) (h : E → ℝ) (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x)
    (hhc : ConvexOn ℝ Q h) : ∀ a ∈ Q, ∀ b ∈ Q, 0 ≤ bregman h b a := by
  intro a ha b hb
  have := RRAux_RSF.grad_of_convexOn h hhc ha hb (hhd a ha)
  simp only [bregman]
  linarith

lemma three_point (Q : Set E) (hQ : Convex ℝ Q) (f h : E → ℝ)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (L : ℝ) (xi xp : E) (hxp : xp ∈ Q)
    (hmin : ∀ u ∈ Q, f xi + fderiv ℝ f xi (xp - xi) + L * bregman h xp xi
      ≤ f xi + fderiv ℝ f xi (u - xi) + L * bregman h u xi) :
    ∀ u ∈ Q, f xi + fderiv ℝ f xi (xp - xi) + L * bregman h xp xi + L * bregman h u xp
      ≤ f xi + fderiv ℝ f xi (u - xi) + L * bregman h u xi := by
  intro u hu
  have a1 : HasFDerivAt (fun v => fderiv ℝ f xi (v - xi)) (fderiv ℝ f xi) xp := by
    exact (fderiv ℝ f xi).hasFDerivAt.comp xp ((hasFDerivAt_id xp).sub_const xi)
  have a2 : HasFDerivAt (fun v => fderiv ℝ h xi (v - xi)) (fderiv ℝ h xi) xp := by
    exact (fderiv ℝ h xi).hasFDerivAt.comp xp ((hasFDerivAt_id xp).sub_const xi)
  have a3 := (((hhd xp hxp).hasFDerivAt.sub_const (h xi)).sub a2).const_mul L
  have hΦ := ((hasFDerivAt_const (f xi) xp).add a1).add a3
  have hmin' : IsMinOn (fun v => f xi + fderiv ℝ f xi (v - xi) +
      L * (h v - h xi - fderiv ℝ h xi (v - xi))) Q xp := by
    intro v hv
    have := hmin v hv
    simp only [bregman] at this
    exact this
  have hnn := hmin'.localize.hasFDerivWithinAt_nonneg hΦ.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (hQ.segment_subset hxp hu))
  have hm := hmin u hu
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul, zero_add] at hnn
  simp only [bregman] at hm ⊢
  simp only [map_sub] at hnn hm ⊢
  linear_combination hnn

end RRAux_PG

open RelSmoothFOM.PrimalGrad in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQ : Convex ℝ Q)
    (f h : E → ℝ) (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hfc : ConvexOn ℝ Q f)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (L μ : ℝ) (hL : 0 < L) (hμ : 0 ≤ μ) (hμL : μ < L)
    (hsm : IsRelSmooth Q f h L) (hsc : IsRelStronglyConvex Q f h μ)
    (x : ℕ → E) (hrun : IsPrimalGradientRun Q f h L x) :
    (∀ i : ℕ, f (x (i + 1)) ≤ f (x i)) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ u ∈ Q,
      f (x k) - f u ≤ (L - μ) / (k : ℝ) * bregman h u (x 0)) ∧
    (0 < μ → ∀ k : ℕ, 1 ≤ k → ∀ u ∈ Q,
      f (x k) - f u ≤ μ * bregman h u (x 0) / ((1 + μ / (L - μ)) ^ k - 1) ∧
      μ * bregman h u (x 0) / ((1 + μ / (L - μ)) ^ k - 1)
        ≤ (L - μ) / (k : ℝ) * bregman h u (x 0)) := by
  obtain ⟨hx0, hstep⟩ := hrun
  have hxQ : ∀ i, x i ∈ Q := fun i => by
    cases i with
    | zero => exact hx0
    | succ n => exact (hstep n).1
  have sm := RRAux_PG.smooth_ext Q hQ f h hfd hhd L hsm
  have sc := RRAux_PG.sc_ext Q hQ f h hfd hhd μ hsc
  have bnn := RRAux_PG.bregman_nonneg Q h hhd hhc
  have K : ∀ u ∈ Q, ∀ i, f (x (i+1)) - f u ≤ L * bregman h u (x i) - μ * bregman h u (x i)
      - L * bregman h u (x (i+1)) := by
    intro u hu i
    have h1 := sm (x i) (hxQ i) (x (i+1)) (hxQ (i+1))
    have h2 := RRAux_PG.three_point Q hQ f h hhd L (x i) (x (i+1)) (hxQ (i+1)) (hstep i).2 u hu
    have h3 := sc (x i) (hxQ i) u hu
    linarith
  have mono : ∀ i, f (x (i+1)) ≤ f (x i) := by
    intro i
    have h1 := K (x i) (hxQ i) i
    have hz : bregman h (x i) (x i) = 0 := by simp [bregman]
    rw [hz] at h1
    have h2 := mul_nonneg hL.le (bnn (x (i+1)) (hxQ (i+1)) (x i) (hxQ i))
    linarith
  have hD : ∀ u ∈ Q, ∀ i, 0 ≤ bregman h u (x i) := fun u hu i => bnn _ (hxQ i) _ hu
  refine ⟨mono, ?_, ?_⟩
  · intro k hk u hu
    exact RRAux_NUM.rate1 L μ hμ hμL (fun i => f (x i) - f u) (fun i => bregman h u (x i))
      (hD u hu) (fun i => by have := K u hu i; linarith)
      (fun i => by have := mono i; linarith) k hk
  · intro hμ0 k hk u hu
    exact RRAux_NUM.rate2 L μ hμ0 hμL (fun i => f (x i) - f u) (fun i => bregman h u (x i))
      (hD u hu) (fun i => by have := K u hu i; linarith)
      (fun i => by have := mono i; linarith) k hk

#print axioms solution
