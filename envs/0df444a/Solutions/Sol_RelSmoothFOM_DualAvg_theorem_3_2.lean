-- Prove2me | solution 1 for RelSmoothFOM.DualAvg.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:25:32.316999+00:00
-- url     : https://prove2.me/submissions/4927f9a2-046e-46ec-b211-5ff4224f2e8c

import Mathlib
import Definitions.Def_RelSmoothFOM_DualAvg_Setting

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

namespace RRAux_DA

open RelSmoothFOM.DualAvg

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


lemma tp_general (Q : Set E) (hQ : Convex ℝ Q) (h : E → ℝ)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (Φ : E → ℝ) (c : ℝ) (Λ : E →L[ℝ] ℝ) (xk : E)
    (hxk : xk ∈ Q) (hmin : ∀ u ∈ Q, Φ xk ≤ Φ u)
    (haff : ∀ u v, (Φ u - c * h u) - (Φ v - c * h v) = Λ (u - v)) :
    ∀ u ∈ Q, Φ xk + c * (h u - h xk - fderiv ℝ h xk (u - xk)) ≤ Φ u := by
  intro u hu
  have hΦeq : Φ = fun v => (Φ xk - c * h xk) + Λ (v - xk) + c * h v := by
    funext v
    have := haff v xk
    linarith
  have a1 : HasFDerivAt (fun v => Λ (v - xk)) Λ xk :=
    Λ.hasFDerivAt.comp xk ((hasFDerivAt_id xk).sub_const xk)
  have hd : HasFDerivAt Φ (0 + Λ + c • fderiv ℝ h xk) xk := by
    rw [hΦeq]
    exact ((hasFDerivAt_const (Φ xk - c * h xk) xk).add a1).add
      ((hhd xk hxk).hasFDerivAt.const_mul c)
  have hmin' : IsMinOn Φ Q xk := fun v hv => hmin v hv
  have hnn := hmin'.localize.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (hQ.segment_subset hxk hu))
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    zero_add] at hnn
  have := haff u xk
  linear_combination hnn - this

lemma model_succ (f h : E → ℝ) (L μ : ℝ) (x : ℕ → E) (k : ℕ) (u : E) :
    daModel f h L μ x (k + 1) u = daModel f h L μ x k u + daWeight L μ k *
      (f (x k) + fderiv ℝ f (x k) (u - x k) + μ * bregman h u (x k)) := by
  simp only [daModel, Finset.sum_range_succ]
  ring

lemma sum_succ (L μ : ℝ) (k : ℕ) : daSum L μ (k + 1) = daSum L μ k + daWeight L μ k := by
  simp only [daSum, Finset.sum_range_succ]

lemma model_aff (f h : E → ℝ) (L μ : ℝ) (x : ℕ → E) (k : ℕ) :
    ∀ u v, (daModel f h L μ x k u - (1 + μ * daSum L μ k) * h u) -
      (daModel f h L μ x k v - (1 + μ * daSum L μ k) * h v) =
      (∑ i ∈ Finset.range k, daWeight L μ i • (fderiv ℝ f (x i) - μ • fderiv ℝ h (x i)))
        (u - v) := by
  induction k with
  | zero => intro u v; simp [daModel, daSum]
  | succ k ih =>
    intro u v
    rw [model_succ, model_succ, Finset.sum_range_succ, ContinuousLinearMap.add_apply, sum_succ]
    have := ih u v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul,
      bregman, map_sub] at this ⊢
    linear_combination this

lemma sum_id (L μ : ℝ) (hμL : μ < L) :
    ∀ k : ℕ, 1 + μ * daSum L μ k = (L / (L - μ)) ^ k := by
  have hLμ : L - μ ≠ 0 := (sub_pos.mpr hμL).ne'
  intro k
  induction k with
  | zero => simp [daSum]
  | succ k ih =>
    rw [sum_succ, pow_succ, ← ih, daWeight, ← ih]
    field_simp
    ring

lemma outer (L μ : ℝ) (hμ : 0 < μ) (hμL : μ < L) (H : ℝ) (hH : 0 ≤ H) (k : ℕ) (hk : 1 ≤ k) :
    μ * H / ((1 + μ / (L - μ)) ^ k - 1) ≤ (L - μ) / k * H := by
  have hLμ : 0 < L - μ := sub_pos.mpr hμL
  have hr0 : 0 < μ / (L - μ) := div_pos hμ hLμ
  have hpow : 1 + (k:ℝ) * (μ / (L - μ)) ≤ (1 + μ / (L - μ)) ^ k :=
    one_add_mul_le_pow (by linarith) k
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  have hkr : 0 < (k:ℝ) * (μ / (L - μ)) := mul_pos hkpos hr0
  calc μ * H / ((1 + μ / (L - μ)) ^ k - 1) ≤ μ * H / ((k:ℝ) * (μ / (L - μ))) :=
        div_le_div_of_nonneg_left (mul_nonneg hμ.le hH) hkr (by linarith)
    _ = (L - μ) / (k : ℝ) * H := by field_simp

end RRAux_DA

open RelSmoothFOM.DualAvg in
theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQ : Convex ℝ Q)
    (f h : E → ℝ) (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hfc : ConvexOn ℝ Q f)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (L μ : ℝ) (hμ : 0 ≤ μ) (hμL : μ < L)
    (hsm : IsRelSmooth Q f h L) (hsc : IsRelStronglyConvex Q f h μ)
    (x : ℕ → E) (hrun : IsDualAveragingRun Q f h L μ x) :
    ∀ k : ℕ, 1 ≤ k → ∀ u ∈ Q,
      (∃ i ∈ Finset.Icc 1 k, f (x i) - f u ≤ (L - μ) / k * h u) ∧
      (0 < μ →
        (∃ i ∈ Finset.Icc 1 k, f (x i) - f u ≤ μ * h u / ((1 + μ / (L - μ)) ^ k - 1)) ∧
        μ * h u / ((1 + μ / (L - μ)) ^ k - 1) ≤ (L - μ) / k * h u) := by
  obtain ⟨hx0, hh0, hhmin, hstep⟩ := hrun
  have hxQ : ∀ i, x i ∈ Q := fun i => by
    cases i with
    | zero => exact hx0
    | succ n => exact (hstep n).1
  have hLμ : 0 < L - μ := sub_pos.mpr hμL
  have hL0 : 0 < L := by linarith
  have sm := RRAux_DA.smooth_ext Q hQ f h hfd hhd L hsm
  have sc := RRAux_DA.sc_ext Q hQ f h hfd hhd μ hsc
  have ha : ∀ i, 0 < daWeight L μ i := fun i =>
    mul_pos (div_pos one_pos hLμ) (pow_pos (div_pos hL0 hLμ) i)
  have hcoef : ∀ k, daWeight L μ k * (L - μ) = 1 + μ * daSum L μ k := by
    intro k
    rw [RRAux_DA.sum_id L μ hμL k, daWeight]
    field_simp
  have hminall : ∀ k, ∀ u ∈ Q, daModel f h L μ x k (x k) ≤ daModel f h L μ x k u := by
    intro k
    cases k with
    | zero =>
      intro u hu
      simp only [daModel, Finset.range_zero, Finset.sum_empty, add_zero]
      exact hhmin u hu
    | succ k => exact (hstep k).2
  have tp : ∀ k, ∀ u ∈ Q, daModel f h L μ x k (x k) + (1 + μ * daSum L μ k) * bregman h u (x k)
      ≤ daModel f h L μ x k u := by
    intro k u hu
    have := RRAux_DA.tp_general Q hQ h hhd (daModel f h L μ x k) (1 + μ * daSum L μ k) _ (x k)
      (hxQ k) (hminall k) (RRAux_DA.model_aff f h L μ x k) u hu
    unfold bregman
    exact this
  have P : ∀ k, ∑ i ∈ Finset.range k, daWeight L μ i * f (x (i+1))
      ≤ daModel f h L μ x k (x k) := by
    intro k
    induction k with
    | zero => simp [daModel, hh0]
    | succ k ih =>
      rw [Finset.sum_range_succ, RRAux_DA.model_succ]
      have t1 := tp k (x (k+1)) (hxQ (k+1))
      have t2 := mul_le_mul_of_nonneg_left (sm (x k) (hxQ k) (x (k+1)) (hxQ (k+1))) (ha k).le
      have t3 := hcoef k
      linear_combination ih + t1 + t2 + (bregman h (x (k+1)) (x k)) * t3
  have upper : ∀ k, ∀ u ∈ Q, daModel f h L μ x k u ≤ h u + daSum L μ k * f u := by
    intro k u hu
    simp only [daModel, daSum, Finset.sum_mul]
    apply add_le_add_right
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (sc (x i) (hxQ i) u hu) (ha i).le
  have hu0 : ∀ u ∈ Q, 0 ≤ h u := fun u hu => hh0 ▸ hhmin u hu
  intro k hk u hu
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  have hA : 0 < daSum L μ k :=
    Finset.sum_pos (fun i _ => ha i) ⟨0, by simp; omega⟩
  obtain ⟨i0, hi0, hmin0⟩ :=
    (Finset.Icc 1 k).exists_min_image (fun i => f (x i)) ⟨1, by simp; omega⟩
  have key : daSum L μ k * (f (x i0) - f u) ≤ h u := by
    have h1 : daSum L μ k * (f (x i0) - f u) ≤
        ∑ i ∈ Finset.range k, daWeight L μ i * (f (x (i+1)) - f u) := by
      rw [daSum, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (ha i).le
      have := hmin0 (i+1) (by simp at hi ⊢; omega)
      linarith
    have h2 : ∑ i ∈ Finset.range k, daWeight L μ i * (f (x (i+1)) - f u) =
        ∑ i ∈ Finset.range k, daWeight L μ i * f (x (i+1)) - daSum L μ k * f u := by
      rw [daSum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h3 := P k
    have h4 := hminall k u hu
    have h5 := upper k u hu
    linarith
  have bound : f (x i0) - f u ≤ h u / daSum L μ k := by
    rw [le_div_iff₀ hA]; linarith [key]
  have hAk : (k:ℝ) / (L - μ) ≤ daSum L μ k := by
    have hw : ∀ i ∈ Finset.range k, 1 / (L - μ) ≤ daWeight L μ i := by
      intro i _
      unfold daWeight
      have : 1 ≤ (L / (L - μ)) ^ i := one_le_pow₀ (by rw [le_div_iff₀ hLμ]; linarith)
      calc 1 / (L - μ) = 1 / (L - μ) * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this (div_pos one_pos hLμ).le
    have := Finset.card_nsmul_le_sum (Finset.range k) _ _ hw
    simp only [Finset.card_range, nsmul_eq_mul] at this
    rw [daSum]
    calc (k:ℝ) / (L - μ) = k * (1 / (L - μ)) := by ring
      _ ≤ _ := this
  have part1 : f (x i0) - f u ≤ (L - μ) / k * h u := by
    calc f (x i0) - f u ≤ h u / daSum L μ k := bound
      _ ≤ h u / (k / (L - μ)) := div_le_div_of_nonneg_left (hu0 u hu) (div_pos hkpos hLμ) hAk
      _ = (L - μ) / k * h u := by field_simp
  refine ⟨⟨i0, hi0, part1⟩, fun hμ0 =>
    ⟨⟨i0, hi0, ?_⟩, RRAux_DA.outer L μ hμ0 hμL (h u) (hu0 u hu) k hk⟩⟩
  have e : (1 + μ / (L - μ)) ^ k - 1 = μ * daSum L μ k := by
    have h1 := RRAux_DA.sum_id L μ hμL k
    have h2 : 1 + μ / (L - μ) = L / (L - μ) := by field_simp; ring
    rw [h2]; linarith
  rw [e, mul_div_mul_left _ _ hμ0.ne']
  exact bound

#print axioms solution
